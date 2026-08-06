// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Solve
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache public import Lean.Elab.Tactic.Do.Internal.VCGen.Entails public import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType import Lean.Meta.Sym.InstantiateMVarsS
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
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorem_global_x3f(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorem_patternMatches(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc;
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitForallLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_outOfFuel_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_outOfFuel_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_untilPatternMatched_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_untilPatternMatched_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noEntailment_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noEntailment_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noProgress_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noProgress_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noSpecFound_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noSpecFound_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_stop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_stop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Failed to intro forall target "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 102, .m_capacity = 102, .m_length = 101, .m_data = "vcgen: shared-continuation handling for `__do_jp` is not yet implemented. Detection point reached at "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 205, .m_capacity = 205, .m_length = 204, .m_data = "; the upstream `Lean.Elab.Tactic.Do.onJoinPoint` (`src/Lean/Elab/Tactic/Do/VCGen.lean:215`) needs to be ported to the worklist style. Drop `(jp := true)` to fall back to the default zeta-unfold behaviour."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-intro: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "let-zeta-dup: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "top"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 33, 148, 124, 218, 91, 248, 169)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rel"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__9_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__9_value),LEAN_SCALAR_PTR_LITERAL(41, 174, 7, 105, 99, 77, 97, 125)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "of_top_le_prop"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__11_value),LEAN_SCALAR_PTR_LITERAL(112, 50, 129, 57, 86, 19, 237, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Solved by rfl "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Solved by lifted hypothesis "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "le_of_right"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 236, 244, 28, 139, 157, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meet"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 193, 63, 6, 53, 61, 199, 176)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 43, .m_data = "Failed to cancel the `⊓ ⊤` precondition of "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofProp"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 160, 150, 32, 134, 96, 114, 42)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropMeetPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "iSup"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(46, 241, 153, 184, 251, 59, 2, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Failed to eliminate the `iSup` precondition of "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object**);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Failed to intro hoisted let"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "let-hoist: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "split rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Failed to apply split rule for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fvar-zeta: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "SpecProof.global "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.local "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "SpecProof.stx _ "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5;
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6_value;
static lean_once_cell_t l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "No spec matching the monad "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = " found for program "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ". Candidates were "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "No spec found for program "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nerror: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\ntarget:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\nPred:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\nexcessArgs: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Failed to construct rule "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nrule type:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "spec rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to apply rule "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Applying spec "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ". Excess args: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`until` pattern matched program "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "; stopping"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`frames` matched "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "; frame:"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PreservesSup"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "upperAdjoint"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 207, 242, 99, 37, 43, 114, 21)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 52, 128, 160, 100, 147, 237, 166)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "frame rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "frame: split VC is not an entailment"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "frame: failed to apply rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`@[frameproc]` matched "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Failed to decompose weakest precondition for "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = ". This should not happen."};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 11, .m_data = "📜 Program: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 10, .m_data = "🎯 Target: "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorIdx___boxed(lean_object* v_x_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorIdx(v_x_7_);
lean_dec(v_x_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(lean_object* v_t_9_, lean_object* v_k_10_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_22_, v_k_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___boxed(lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim(v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_outOfFuel_elim___redArg(lean_object* v_t_32_, lean_object* v_outOfFuel_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_32_, v_outOfFuel_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_outOfFuel_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_outOfFuel_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_36_, v_outOfFuel_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_untilPatternMatched_elim___redArg(lean_object* v_t_40_, lean_object* v_untilPatternMatched_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_40_, v_untilPatternMatched_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_untilPatternMatched_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_untilPatternMatched_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_44_, v_untilPatternMatched_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noEntailment_elim___redArg(lean_object* v_t_48_, lean_object* v_noEntailment_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_48_, v_noEntailment_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noEntailment_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_noEntailment_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_52_, v_noEntailment_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noProgress_elim___redArg(lean_object* v_t_56_, lean_object* v_noProgress_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_56_, v_noProgress_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noProgress_elim(lean_object* v_motive_59_, lean_object* v_t_60_, lean_object* v_h_61_, lean_object* v_noProgress_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_60_, v_noProgress_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noSpecFound_elim___redArg(lean_object* v_t_64_, lean_object* v_noSpecFound_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_64_, v_noSpecFound_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_noSpecFound_elim(lean_object* v_motive_67_, lean_object* v_t_68_, lean_object* v_h_69_, lean_object* v_noSpecFound_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_StopReason_ctorElim___redArg(v_t_68_, v_noSpecFound_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(lean_object* v_x_72_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx___boxed(lean_object* v_x_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorIdx(v_x_75_);
lean_dec_ref(v_x_75_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(lean_object* v_t_77_, lean_object* v_k_78_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(lean_object* v_motive_84_, lean_object* v_ctorIdx_85_, lean_object* v_t_86_, lean_object* v_h_87_, lean_object* v_k_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_86_, v_k_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___boxed(lean_object* v_motive_90_, lean_object* v_ctorIdx_91_, lean_object* v_t_92_, lean_object* v_h_93_, lean_object* v_k_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim(v_motive_90_, v_ctorIdx_91_, v_t_92_, v_h_93_, v_k_94_);
lean_dec(v_ctorIdx_91_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim___redArg(lean_object* v_t_96_, lean_object* v_goals_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_96_, v_goals_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_goals_elim(lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_goals_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_100_, v_goals_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_stop_elim___redArg(lean_object* v_t_104_, lean_object* v_stop_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_104_, v_stop_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_stop_elim(lean_object* v_motive_107_, lean_object* v_t_108_, lean_object* v_h_109_, lean_object* v_stop_110_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_SolveResult_ctorElim___redArg(v_t_108_, v_stop_110_);
return v___x_111_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(lean_object* v_e_117_){
_start:
{
switch(lean_obj_tag(v_e_117_))
{
case 5:
{
lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___closed__2));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable___boxed(lean_object* v_e_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_e_128_);
lean_dec_ref(v_e_128_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg(lean_object* v_goal_131_, lean_object* v_target_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg___boxed(lean_object* v_goal_160_, lean_object* v_target_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg(v_goal_160_, v_target_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_);
lean_dec(v_a_165_);
lean_dec_ref(v_a_164_);
lean_dec(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec_ref(v_target_161_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f(lean_object* v_goal_168_, lean_object* v_target_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg(v_goal_168_, v_target_169_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___boxed(lean_object* v_goal_183_, lean_object* v_target_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f(v_goal_183_, v_target_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(lean_object* v_msgData_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msgData_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(lean_object* v_msg_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_ref_226_; lean_object* v___x_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_ref_226_ = lean_ctor_get(v___y_223_, 5);
v___x_227_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_243_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1));
v___x_248_ = l_Lean_stringToMessageData(v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(lean_object* v_goal_251_, lean_object* v_target_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_){
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
v___x_274_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_251_, v_a_253_, v_a_254_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_);
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
v___x_320_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
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
v___x_293_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
lean_inc(v_fst_280_);
v___x_294_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_fst_280_, v___x_293_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
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
v___x_298_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2);
v___x_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_299_, 0, v_fst_280_);
v___x_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_298_);
lean_ctor_set(v___x_300_, 1, v___x_299_);
v___x_301_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_300_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___boxed(lean_object* v_goal_334_, lean_object* v_target_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_334_, v_target_335_, v_a_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(lean_object* v_00_u03b1_349_, lean_object* v_msg_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_350_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___boxed(lean_object* v_00_u03b1_364_, lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(v_00_u03b1_364_, v_msg_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1(void){
_start:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0));
v___x_381_ = l_Lean_stringToMessageData(v___x_380_);
return v___x_381_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3(void){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__2));
v___x_384_ = l_Lean_stringToMessageData(v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(lean_object* v_name_385_, lean_object* v_val_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
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
v___x_399_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1);
v___x_400_ = l_Lean_MessageData_ofName(v_name_385_);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3);
v___x_403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_403_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___boxed(lean_object* v_name_405_, lean_object* v_val_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_name_405_, v_val_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_);
lean_dec(v_a_411_);
lean_dec_ref(v_a_410_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec_ref(v_val_406_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(lean_object* v_name_414_, lean_object* v_val_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_name_414_, v_val_415_, v_a_416_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___boxed(lean_object* v_name_429_, lean_object* v_val_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(v_name_429_, v_val_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
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
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_444_; double v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_float_of_nat(v___x_444_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object* v_cls_449_, lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_ref_456_; lean_object* v___x_457_; lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_502_; 
v_ref_456_ = lean_ctor_get(v___y_453_, 5);
v___x_457_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
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
v___x_481_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0);
v___x_482_ = 0;
v___x_483_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1));
v___x_484_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_484_, 0, v_cls_449_);
lean_ctor_set(v___x_484_, 1, v___x_480_);
lean_ctor_set(v___x_484_, 2, v___x_483_);
lean_ctor_set_float(v___x_484_, sizeof(void*)*3, v___x_481_);
lean_ctor_set_float(v___x_484_, sizeof(void*)*3 + 8, v___x_481_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*3 + 16, v___x_482_);
v___x_485_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2));
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
v___x_493_ = lean_st_ref_set(v___y_454_, v___x_492_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object* v_cls_503_, lean_object* v_msg_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_503_, v_msg_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
return v_res_510_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7(void){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__6));
v___x_525_ = l_Lean_Name_append(v___x_524_, v___x_523_);
return v___x_525_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__8));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__10));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(lean_object* v_goal_532_, lean_object* v_target_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_, lean_object* v_a_544_){
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
v___x_618_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_577_, v_value_578_, v_a_534_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
if (lean_obj_tag(v___x_618_) == 0)
{
uint8_t v___x_619_; 
lean_dec_ref_known(v___x_618_, 1);
v___x_619_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_578_);
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
v___x_623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_624_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
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
v___x_626_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9);
v___x_627_ = l_Lean_MessageData_ofName(v_declName_577_);
v___x_628_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
v___x_629_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_623_, v___x_628_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
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
v___x_641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_642_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
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
v___x_644_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_645_ = l_Lean_MessageData_ofName(v_declName_577_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_641_, v___x_646_, v_a_541_, v_a_542_, v_a_543_, v_a_544_);
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
v___x_558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_559_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_goal_532_, v___x_558_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___boxed(lean_object* v_goal_666_, lean_object* v_target_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_666_, v_target_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(lean_object* v_cls_681_, lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_681_, v_msg_682_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object* v_cls_696_, lean_object* v_msg_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(v_cls_696_, v_msg_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(lean_object* v_goal_719_, lean_object* v_target_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3));
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
v___x_737_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(v_goal_719_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_755_, lean_object* v_target_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_755_, v_target_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_x_773_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_800_, lean_object* v_k_801_, lean_object* v_v_802_){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_unsigned_to_nat(0u);
v___x_804_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_800_, v___x_803_, v_k_801_, v_v_802_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_806_, size_t v_x_807_, size_t v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_){
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
v___x_849_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_841_, v___x_846_, v___x_848_, v_x_809_, v_x_810_);
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
v_newNode_864_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_863_, v_x_809_, v_x_810_);
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
v___x_870_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_871_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_808_, v_ks_867_, v_vs_868_, v___x_869_, v___x_870_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_879_, lean_object* v_keys_880_, lean_object* v_vals_881_, lean_object* v_i_882_, lean_object* v_entries_883_){
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
v___x_897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_883_, v_h_895_, v_depth_879_, v_k_886_, v_v_887_);
v_i_882_ = v___x_896_;
v_entries_883_ = v___x_897_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_899_, lean_object* v_keys_900_, lean_object* v_vals_901_, lean_object* v_i_902_, lean_object* v_entries_903_){
_start:
{
size_t v_depth_boxed_904_; lean_object* v_res_905_; 
v_depth_boxed_904_ = lean_unbox_usize(v_depth_899_);
lean_dec(v_depth_899_);
v_res_905_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_904_, v_keys_900_, v_vals_901_, v_i_902_, v_entries_903_);
lean_dec_ref(v_vals_901_);
lean_dec_ref(v_keys_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
size_t v_x_8514__boxed_911_; size_t v_x_8515__boxed_912_; lean_object* v_res_913_; 
v_x_8514__boxed_911_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_x_8515__boxed_912_ = lean_unbox_usize(v_x_908_);
lean_dec(v_x_908_);
v_res_913_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_906_, v_x_8514__boxed_911_, v_x_8515__boxed_912_, v_x_909_, v_x_910_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
uint64_t v___x_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___x_917_ = l_Lean_instHashableMVarId_hash(v_x_915_);
v___x_918_ = lean_uint64_to_usize(v___x_917_);
v___x_919_ = ((size_t)1ULL);
v___x_920_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_914_, v___x_918_, v___x_919_, v_x_915_, v_x_916_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_921_, lean_object* v_val_922_, lean_object* v___y_923_){
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
v___x_947_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_942_, v_mvarId_921_, v_val_922_);
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
v___x_952_ = lean_st_ref_set(v___y_923_, v___x_951_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_959_, lean_object* v_val_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_959_, v_val_960_, v___y_961_);
lean_dec(v___y_961_);
return v_res_963_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_unsigned_to_nat(0u);
v___x_972_ = l_Lean_Level_ofNat(v___x_971_);
return v___x_972_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_973_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4);
v___x_974_ = l_Lean_mkSort(v___x_973_);
return v___x_974_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5);
v___x_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_977_ = lean_box(0);
v___x_978_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6);
v___x_979_ = lean_unsigned_to_nat(2u);
v___x_980_ = lean_mk_empty_array_with_capacity(v___x_979_);
v___x_981_ = lean_array_push(v___x_980_, v___x_978_);
v___x_982_ = lean_array_push(v___x_981_, v___x_977_);
return v___x_982_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_995_ = lean_box(0);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12));
v___x_997_ = l_Lean_mkConst(v___x_996_, v___x_995_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(lean_object* v_goal_998_, lean_object* v_target_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v___x_1012_; 
lean_inc_ref(v_target_999_);
v___x_1012_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(v_target_999_);
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
v___x_1016_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1017_ = lean_unsigned_to_nat(2u);
v___x_1018_ = lean_mk_empty_array_with_capacity(v___x_1017_);
v___x_1019_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7);
v___x_1020_ = l_Lean_Meta_mkAppOptM(v___x_1016_, v___x_1019_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec_ref_known(v___x_1020_, 1);
v___x_1022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
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
v___x_1032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13);
v___x_1033_ = l_Lean_mkAppB(v___x_1032_, v_target_999_, v_a_1031_);
v___x_1034_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_998_, v___x_1033_, v_a_1008_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1083_, lean_object* v_target_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_1083_, v_target_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1098_, lean_object* v_val_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1098_, v_val_1099_, v___y_1108_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1113_, lean_object* v_val_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1113_, v_val_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1129_, v_x_1130_, v_x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, size_t v_x_1135_, size_t v_x_1136_, lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1134_, v_x_1135_, v_x_1136_, v_x_1137_, v_x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_, lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
size_t v_x_9024__boxed_1146_; size_t v_x_9025__boxed_1147_; lean_object* v_res_1148_; 
v_x_9024__boxed_1146_ = lean_unbox_usize(v_x_1142_);
lean_dec(v_x_1142_);
v_x_9025__boxed_1147_ = lean_unbox_usize(v_x_1143_);
lean_dec(v_x_1143_);
v_res_1148_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1140_, v_x_1141_, v_x_9024__boxed_1146_, v_x_9025__boxed_1147_, v_x_1144_, v_x_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1149_, lean_object* v_n_1150_, lean_object* v_k_1151_, lean_object* v_v_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1150_, v_k_1151_, v_v_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1154_, size_t v_depth_1155_, lean_object* v_keys_1156_, lean_object* v_vals_1157_, lean_object* v_heq_1158_, lean_object* v_i_1159_, lean_object* v_entries_1160_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1155_, v_keys_1156_, v_vals_1157_, v_i_1159_, v_entries_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1162_, lean_object* v_depth_1163_, lean_object* v_keys_1164_, lean_object* v_vals_1165_, lean_object* v_heq_1166_, lean_object* v_i_1167_, lean_object* v_entries_1168_){
_start:
{
size_t v_depth_boxed_1169_; lean_object* v_res_1170_; 
v_depth_boxed_1169_ = lean_unbox_usize(v_depth_1163_);
lean_dec(v_depth_1163_);
v_res_1170_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1162_, v_depth_boxed_1169_, v_keys_1164_, v_vals_1165_, v_heq_1166_, v_i_1167_, v_entries_1168_);
lean_dec_ref(v_vals_1165_);
lean_dec_ref(v_keys_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1172_, v_x_1173_, v_x_1174_, v_x_1175_);
return v___x_1176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0));
v___x_1179_ = l_Lean_stringToMessageData(v___x_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(lean_object* v_goal_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
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
v___x_1210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1211_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1212_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1209_, v_options_1207_, v___x_1211_);
if (v___x_1212_ == 0)
{
lean_dec(v_goal_1180_);
goto v___jp_1200_;
}
else
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1);
v___x_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1214_, 0, v_goal_1180_);
v___x_1215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1213_);
lean_ctor_set(v___x_1215_, 1, v___x_1214_);
v___x_1216_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1210_, v___x_1215_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(lean_object* v_goal_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1249_, v_a_1250_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___boxed(lean_object* v_goal_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(v_goal_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1279_ = l_Lean_stringToMessageData(v___x_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1280_, lean_object* v_e_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
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
v___x_1314_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1315_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
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
v___x_1320_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1321_ = l_Lean_LocalDecl_userName(v_val_1294_);
lean_dec(v_val_1294_);
v___x_1322_ = l_Lean_MessageData_ofName(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1320_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1314_, v___x_1323_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1348_, lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v_res_1355_; 
v_res_1355_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1348_, v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec_ref(v_a_1350_);
lean_dec_ref(v_e_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(lean_object* v_scope_1356_, lean_object* v_e_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1356_, v_e_1357_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1371_, lean_object* v_e_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_, lean_object* v_a_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(v_scope_1371_, v_e_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_, v_a_1377_, v_a_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1414_, lean_object* v_x_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
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
v___f_1428_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1438_, lean_object* v_x_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1438_, v_x_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1453_, lean_object* v_mvarId_1454_, lean_object* v_x_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1454_, v_x_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1469_, lean_object* v_mvarId_1470_, lean_object* v_x_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1469_, v_mvarId_1470_, v_x_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1490_, lean_object* v_scope_1491_, lean_object* v_rhs_1492_, lean_object* v_pre_1493_, lean_object* v_goal_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
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
v___x_1509_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1491_, v_rhs_1492_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
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
v___x_1515_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1));
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
v___x_1524_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1494_, v_a_1523_, v___y_1503_);
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
v___x_1528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
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
v_res_1573_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1572_, v_scope_1556_, v_rhs_1557_, v_pre_1558_, v_goal_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(lean_object* v_scope_1574_, lean_object* v_goal_1575_, lean_object* v_00_u03b1_1576_, lean_object* v_pre_1577_, lean_object* v_rhs_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_){
_start:
{
uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___y_1593_; lean_object* v___x_1594_; 
v___x_1591_ = l_Lean_Expr_isProp(v_00_u03b1_1576_);
v___x_1592_ = lean_box(v___x_1591_);
lean_inc(v_goal_1575_);
v___y_1593_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1593_, 0, v___x_1592_);
lean_closure_set(v___y_1593_, 1, v_scope_1574_);
lean_closure_set(v___y_1593_, 2, v_rhs_1578_);
lean_closure_set(v___y_1593_, 3, v_pre_1577_);
lean_closure_set(v___y_1593_, 4, v_goal_1575_);
v___x_1594_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1575_, v___y_1593_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
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
v_res_1612_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_scope_1595_, v_goal_1596_, v_00_u03b1_1597_, v_pre_1598_, v_rhs_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1613_, lean_object* v_target_1614_, lean_object* v_goal_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1613_, v_target_1614_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_);
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
v___x_1635_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1615_, v___x_1634_, v___y_1624_);
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
v___x_1639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1658_, lean_object* v_target_1659_, lean_object* v_goal_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v_res_1673_; 
v_res_1673_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(v_scope_1658_, v_target_1659_, v_goal_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(lean_object* v_scope_1674_, lean_object* v_goal_1675_, lean_object* v_target_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v___f_1689_; lean_object* v___x_1690_; 
lean_inc(v_goal_1675_);
v___f_1689_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1689_, 0, v_scope_1674_);
lean_closure_set(v___f_1689_, 1, v_target_1676_);
lean_closure_set(v___f_1689_, 2, v_goal_1675_);
v___x_1690_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1675_, v___f_1689_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1691_, lean_object* v_goal_1692_, lean_object* v_target_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_1691_, v_goal_1692_, v_target_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_, v_a_1704_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1707_, lean_object* v_a_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___y_1717_; lean_object* v___x_1720_; uint8_t v_debug_1721_; 
v___x_1720_ = lean_st_ref_get(v___y_1710_);
v_debug_1721_ = lean_ctor_get_uint8(v___x_1720_, sizeof(void*)*11);
lean_dec(v___x_1720_);
if (v_debug_1721_ == 0)
{
v___y_1717_ = v___y_1710_;
goto v___jp_1716_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_1707_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v___x_1723_; 
lean_dec_ref_known(v___x_1722_, 1);
v___x_1723_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_dec_ref_known(v___x_1723_, 1);
v___y_1717_ = v___y_1710_;
goto v___jp_1716_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1731_; 
lean_dec_ref(v_a_1708_);
lean_dec_ref(v_f_1707_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1726_ = v___x_1723_;
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_a_1724_);
lean_dec(v___x_1723_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1731_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1729_; 
if (v_isShared_1727_ == 0)
{
v___x_1729_ = v___x_1726_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_a_1724_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
return v___x_1729_;
}
}
}
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v_a_1708_);
lean_dec_ref(v_f_1707_);
v_a_1732_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1722_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1722_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
v___jp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = l_Lean_Expr_app___override(v_f_1707_, v_a_1708_);
v___x_1719_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1718_, v___y_1717_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1740_, lean_object* v_a_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_1740_, v_a_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0(lean_object* v_args_1750_, lean_object* v_endIdx_1751_, lean_object* v_b_1752_, lean_object* v_i_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_nat_dec_le(v_endIdx_1751_, v_i_1753_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = l_Lean_instInhabitedExpr;
v___x_1768_ = lean_array_get_borrowed(v___x_1767_, v_args_1750_, v_i_1753_);
lean_inc(v___x_1768_);
v___x_1769_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_1752_, v___x_1768_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = lean_nat_add(v_i_1753_, v___x_1771_);
lean_dec(v_i_1753_);
v_b_1752_ = v_a_1770_;
v_i_1753_ = v___x_1772_;
goto _start;
}
else
{
lean_dec(v_i_1753_);
return v___x_1769_;
}
}
else
{
lean_object* v___x_1774_; 
lean_dec(v_i_1753_);
v___x_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1774_, 0, v_b_1752_);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0___boxed(lean_object* v_args_1775_, lean_object* v_endIdx_1776_, lean_object* v_b_1777_, lean_object* v_i_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1775_, v_endIdx_1776_, v_b_1777_, v_i_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_);
lean_dec(v___y_1789_);
lean_dec_ref(v___y_1788_);
lean_dec(v___y_1787_);
lean_dec_ref(v___y_1786_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v_endIdx_1776_);
lean_dec_ref(v_args_1775_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(lean_object* v_f_1792_, lean_object* v_args_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_size(v_args_1793_);
v___x_1808_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0(v_args_1793_, v___x_1807_, v_f_1792_, v___x_1806_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0___boxed(lean_object* v_f_1809_, lean_object* v_args_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v_f_1809_, v_args_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
lean_dec(v___y_1821_);
lean_dec_ref(v___y_1820_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec_ref(v_args_1810_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f(lean_object* v_goal_1824_, lean_object* v_target_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = l_Lean_Expr_cleanupAnnotations(v_target_1825_);
v___x_1842_ = l_Lean_Expr_isApp(v___x_1841_);
if (v___x_1842_ == 0)
{
lean_dec_ref(v___x_1841_);
lean_dec(v_goal_1824_);
goto v___jp_1838_;
}
else
{
lean_object* v_arg_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_arg_1843_ = lean_ctor_get(v___x_1841_, 1);
lean_inc_ref(v_arg_1843_);
v___x_1844_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1841_);
v___x_1845_ = l_Lean_Expr_isApp(v___x_1844_);
if (v___x_1845_ == 0)
{
lean_dec_ref(v___x_1844_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
goto v___jp_1838_;
}
else
{
lean_object* v_arg_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_arg_1846_ = lean_ctor_get(v___x_1844_, 1);
lean_inc_ref(v_arg_1846_);
v___x_1847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1844_);
v___x_1848_ = l_Lean_Expr_isApp(v___x_1847_);
if (v___x_1848_ == 0)
{
lean_dec_ref(v___x_1847_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
goto v___jp_1838_;
}
else
{
lean_object* v_arg_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v_arg_1849_ = lean_ctor_get(v___x_1847_, 1);
lean_inc_ref(v_arg_1849_);
v___x_1850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1847_);
v___x_1851_ = l_Lean_Expr_isApp(v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec_ref(v___x_1850_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
goto v___jp_1838_;
}
else
{
lean_object* v_arg_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_arg_1852_ = lean_ctor_get(v___x_1850_, 1);
lean_inc_ref(v_arg_1852_);
v___x_1853_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1850_);
v___x_1854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_1855_ = l_Lean_Expr_isConstOf(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
goto v___jp_1838_;
}
else
{
lean_object* v___x_1856_; 
lean_inc_ref(v_arg_1852_);
v___x_1856_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1852_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
lean_inc_ref(v_arg_1846_);
v___x_1858_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1846_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v_a_1859_; lean_object* v___x_1860_; 
v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
lean_inc(v_a_1859_);
lean_dec_ref_known(v___x_1858_, 1);
lean_inc_ref(v_arg_1843_);
v___x_1860_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_1843_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1915_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1915_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1915_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
uint8_t v___y_1901_; size_t v___x_1909_; size_t v___x_1910_; uint8_t v___x_1911_; 
v___x_1909_ = lean_ptr_addr(v_arg_1852_);
lean_dec_ref(v_arg_1852_);
v___x_1910_ = lean_ptr_addr(v_a_1857_);
v___x_1911_ = lean_usize_dec_eq(v___x_1909_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v_arg_1846_);
v___y_1901_ = v___x_1911_;
goto v___jp_1900_;
}
else
{
size_t v___x_1912_; size_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = lean_ptr_addr(v_arg_1846_);
lean_dec_ref(v_arg_1846_);
v___x_1913_ = lean_ptr_addr(v_a_1859_);
v___x_1914_ = lean_usize_dec_eq(v___x_1912_, v___x_1913_);
v___y_1901_ = v___x_1914_;
goto v___jp_1900_;
}
v___jp_1865_:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1866_ = lean_unsigned_to_nat(4u);
v___x_1867_ = lean_mk_empty_array_with_capacity(v___x_1866_);
v___x_1868_ = lean_array_push(v___x_1867_, v_a_1857_);
v___x_1869_ = lean_array_push(v___x_1868_, v_arg_1849_);
v___x_1870_ = lean_array_push(v___x_1869_, v_a_1859_);
v___x_1871_ = lean_array_push(v___x_1870_, v_a_1861_);
v___x_1872_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v___x_1853_, v___x_1871_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec_ref(v___x_1871_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1874_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_1824_, v_a_1873_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1883_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1877_ = v___x_1874_;
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1883_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_a_1875_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v___x_1879_);
v___x_1881_ = v___x_1877_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
v_a_1884_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1874_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1874_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_goal_1824_);
v_a_1892_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1872_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1872_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
v___jp_1900_:
{
if (v___y_1901_ == 0)
{
lean_del_object(v___x_1863_);
lean_dec_ref(v_arg_1843_);
goto v___jp_1865_;
}
else
{
size_t v___x_1902_; size_t v___x_1903_; uint8_t v___x_1904_; 
v___x_1902_ = lean_ptr_addr(v_arg_1843_);
lean_dec_ref(v_arg_1843_);
v___x_1903_ = lean_ptr_addr(v_a_1861_);
v___x_1904_ = lean_usize_dec_eq(v___x_1902_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_del_object(v___x_1863_);
goto v___jp_1865_;
}
else
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
lean_dec(v_a_1861_);
lean_dec(v_a_1859_);
lean_dec(v_a_1857_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1849_);
lean_dec(v_goal_1824_);
v___x_1905_ = lean_box(0);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v___x_1905_);
v___x_1907_ = v___x_1863_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1859_);
lean_dec(v_a_1857_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
v_a_1916_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1860_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1860_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec(v_a_1857_);
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
v_a_1924_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1858_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1858_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___x_1853_);
lean_dec_ref(v_arg_1852_);
lean_dec_ref(v_arg_1849_);
lean_dec_ref(v_arg_1846_);
lean_dec_ref(v_arg_1843_);
lean_dec(v_goal_1824_);
v_a_1932_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1856_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1856_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
}
}
}
v___jp_1838_:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_box(0);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f___boxed(lean_object* v_goal_1940_, lean_object* v_target_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f(v_goal_1940_, v_target_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_);
lean_dec(v_a_1952_);
lean_dec_ref(v_a_1951_);
lean_dec(v_a_1950_);
lean_dec_ref(v_a_1949_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(lean_object* v_f_1955_, lean_object* v_a_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_f_1955_, v_a_1956_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_f_1970_, lean_object* v_a_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1(v_f_1970_, v_a_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1984_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_1992_ = l_Lean_stringToMessageData(v___x_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_1993_, lean_object* v_pre_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = l_Lean_Expr_cleanupAnnotations(v_pre_1994_);
v___x_2011_ = l_Lean_Expr_isApp(v___x_2010_);
if (v___x_2011_ == 0)
{
lean_dec_ref(v___x_2010_);
lean_dec(v_goal_1993_);
goto v___jp_2007_;
}
else
{
lean_object* v_arg_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v_arg_2012_ = lean_ctor_get(v___x_2010_, 1);
lean_inc_ref(v_arg_2012_);
v___x_2013_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2010_);
v___x_2014_ = l_Lean_Expr_isApp(v___x_2013_);
if (v___x_2014_ == 0)
{
lean_dec_ref(v___x_2013_);
lean_dec_ref(v_arg_2012_);
lean_dec(v_goal_1993_);
goto v___jp_2007_;
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2013_);
v___x_2016_ = l_Lean_Expr_isApp(v___x_2015_);
if (v___x_2016_ == 0)
{
lean_dec_ref(v___x_2015_);
lean_dec_ref(v_arg_2012_);
lean_dec(v_goal_1993_);
goto v___jp_2007_;
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2015_);
v___x_2018_ = l_Lean_Expr_isApp(v___x_2017_);
if (v___x_2018_ == 0)
{
lean_dec_ref(v___x_2017_);
lean_dec_ref(v_arg_2012_);
lean_dec(v_goal_1993_);
goto v___jp_2007_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2019_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2017_);
v___x_2020_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2021_ = l_Lean_Expr_isConstOf(v___x_2019_, v___x_2020_);
lean_dec_ref(v___x_2019_);
if (v___x_2021_ == 0)
{
lean_dec_ref(v_arg_2012_);
lean_dec(v_goal_1993_);
goto v___jp_2007_;
}
else
{
lean_object* v___x_2022_; uint8_t v___x_2023_; 
v___x_2022_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_2023_ = l_Lean_Expr_isAppOf(v_arg_2012_, v___x_2022_);
lean_dec_ref(v_arg_2012_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
lean_dec(v_goal_1993_);
v___x_2024_ = lean_box(0);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
else
{
lean_object* v_backwardRules_2026_; lean_object* v_meetTop_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_backwardRules_2026_ = lean_ctor_get(v_a_1995_, 0);
v_meetTop_2027_ = lean_ctor_get(v_backwardRules_2026_, 10);
v___x_2028_ = lean_box(0);
lean_inc(v_goal_1993_);
lean_inc_ref(v_meetTop_2027_);
v___x_2029_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_2027_, v_goal_1993_, v___x_2028_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2056_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2032_ = v___x_2029_;
v_isShared_2033_ = v_isSharedCheck_2056_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2029_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2056_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; 
if (lean_obj_tag(v_a_2030_) == 1)
{
lean_object* v_mvarIds_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2055_; 
v_mvarIds_2043_ = lean_ctor_get(v_a_2030_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_a_2030_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2045_ = v_a_2030_;
v_isShared_2046_ = v_isSharedCheck_2055_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_mvarIds_2043_);
lean_dec(v_a_2030_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2055_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
if (lean_obj_tag(v_mvarIds_2043_) == 1)
{
lean_object* v_tail_2047_; 
v_tail_2047_ = lean_ctor_get(v_mvarIds_2043_, 1);
if (lean_obj_tag(v_tail_2047_) == 0)
{
lean_object* v_head_2048_; lean_object* v___x_2050_; 
lean_dec(v_goal_1993_);
v_head_2048_ = lean_ctor_get(v_mvarIds_2043_, 0);
lean_inc(v_head_2048_);
lean_dec_ref_known(v_mvarIds_2043_, 2);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v_head_2048_);
v___x_2050_ = v___x_2045_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_head_2048_);
v___x_2050_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
lean_object* v___x_2052_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2050_);
v___x_2052_ = v___x_2032_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2043_, 2);
lean_del_object(v___x_2045_);
lean_del_object(v___x_2032_);
v___y_2035_ = v_a_2002_;
v___y_2036_ = v_a_2003_;
v___y_2037_ = v_a_2004_;
v___y_2038_ = v_a_2005_;
goto v___jp_2034_;
}
}
else
{
lean_del_object(v___x_2045_);
lean_dec(v_mvarIds_2043_);
lean_del_object(v___x_2032_);
v___y_2035_ = v_a_2002_;
v___y_2036_ = v_a_2003_;
v___y_2037_ = v_a_2004_;
v___y_2038_ = v_a_2005_;
goto v___jp_2034_;
}
}
}
else
{
lean_del_object(v___x_2032_);
lean_dec(v_a_2030_);
v___y_2035_ = v_a_2002_;
v___y_2036_ = v_a_2003_;
v___y_2037_ = v_a_2004_;
v___y_2038_ = v_a_2005_;
goto v___jp_2034_;
}
v___jp_2034_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2039_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_goal_1993_);
v___x_2041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2041_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2042_;
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_goal_1993_);
v_a_2057_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2029_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2029_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
}
}
}
}
v___jp_2007_:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_box(0);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_2065_, lean_object* v_pre_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_2065_, v_pre_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_, v_a_2072_, v_a_2073_, v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2072_);
lean_dec(v_a_2071_);
lean_dec_ref(v_a_2070_);
lean_dec(v_a_2069_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_2087_, lean_object* v_pre_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_){
_start:
{
lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2104_ = l_Lean_Expr_cleanupAnnotations(v_pre_2088_);
v___x_2105_ = l_Lean_Expr_isApp(v___x_2104_);
if (v___x_2105_ == 0)
{
lean_dec_ref(v___x_2104_);
lean_dec(v_goal_2087_);
goto v___jp_2101_;
}
else
{
lean_object* v_arg_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_arg_2106_ = lean_ctor_get(v___x_2104_, 1);
lean_inc_ref(v_arg_2106_);
v___x_2107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2104_);
v___x_2108_ = l_Lean_Expr_isApp(v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec_ref(v___x_2107_);
lean_dec_ref(v_arg_2106_);
lean_dec(v_goal_2087_);
goto v___jp_2101_;
}
else
{
lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2107_);
v___x_2110_ = l_Lean_Expr_isApp(v___x_2109_);
if (v___x_2110_ == 0)
{
lean_dec_ref(v___x_2109_);
lean_dec_ref(v_arg_2106_);
lean_dec(v_goal_2087_);
goto v___jp_2101_;
}
else
{
lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2109_);
v___x_2112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2113_ = l_Lean_Expr_isConstOf(v___x_2111_, v___x_2112_);
lean_dec_ref(v___x_2111_);
if (v___x_2113_ == 0)
{
lean_dec_ref(v_arg_2106_);
lean_dec(v_goal_2087_);
goto v___jp_2101_;
}
else
{
uint8_t v___x_2114_; 
v___x_2114_ = l_Lean_Expr_isTrue(v_arg_2106_);
if (v___x_2114_ == 0)
{
lean_object* v_backwardRules_2115_; lean_object* v_ofPropPreIntro_2116_; lean_object* v___x_2117_; 
v_backwardRules_2115_ = lean_ctor_get(v_a_2089_, 0);
v_ofPropPreIntro_2116_ = lean_ctor_get(v_backwardRules_2115_, 3);
lean_inc_ref(v_ofPropPreIntro_2116_);
v___x_2117_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_ofPropPreIntro_2116_, v_goal_2087_, v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2126_; 
v_a_2118_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2120_ = v___x_2117_;
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2117_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2126_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v_a_2118_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2124_ = v___x_2120_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
v_a_2127_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2117_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2117_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
lean_dec(v_goal_2087_);
v___x_2135_ = lean_box(0);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
}
}
}
}
v___jp_2101_:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = lean_box(0);
v___x_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_2137_, lean_object* v_pre_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_2137_, v_pre_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropMeetPreIntro_x3f(lean_object* v_goal_2152_, lean_object* v_pre_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_, lean_object* v_a_2157_, lean_object* v_a_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = l_Lean_Expr_cleanupAnnotations(v_pre_2153_);
v___x_2173_ = l_Lean_Expr_isApp(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_dec_ref(v___x_2172_);
lean_dec(v_goal_2152_);
goto v___jp_2166_;
}
else
{
lean_object* v___x_2174_; uint8_t v___x_2175_; 
v___x_2174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2172_);
v___x_2175_ = l_Lean_Expr_isApp(v___x_2174_);
if (v___x_2175_ == 0)
{
lean_dec_ref(v___x_2174_);
lean_dec(v_goal_2152_);
goto v___jp_2166_;
}
else
{
lean_object* v_arg_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v_arg_2176_ = lean_ctor_get(v___x_2174_, 1);
lean_inc_ref(v_arg_2176_);
v___x_2177_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2174_);
v___x_2178_ = l_Lean_Expr_isApp(v___x_2177_);
if (v___x_2178_ == 0)
{
lean_dec_ref(v___x_2177_);
lean_dec_ref(v_arg_2176_);
lean_dec(v_goal_2152_);
goto v___jp_2166_;
}
else
{
lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2177_);
v___x_2180_ = l_Lean_Expr_isApp(v___x_2179_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v___x_2179_);
lean_dec_ref(v_arg_2176_);
lean_dec(v_goal_2152_);
goto v___jp_2166_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v___x_2181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2179_);
v___x_2182_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_2183_ = l_Lean_Expr_isConstOf(v___x_2181_, v___x_2182_);
lean_dec_ref(v___x_2181_);
if (v___x_2183_ == 0)
{
lean_dec_ref(v_arg_2176_);
lean_dec(v_goal_2152_);
goto v___jp_2166_;
}
else
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = l_Lean_Expr_cleanupAnnotations(v_arg_2176_);
v___x_2185_ = l_Lean_Expr_isApp(v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec_ref(v___x_2184_);
lean_dec(v_goal_2152_);
goto v___jp_2169_;
}
else
{
lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2184_);
v___x_2187_ = l_Lean_Expr_isApp(v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec_ref(v___x_2186_);
lean_dec(v_goal_2152_);
goto v___jp_2169_;
}
else
{
lean_object* v___x_2188_; uint8_t v___x_2189_; 
v___x_2188_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2186_);
v___x_2189_ = l_Lean_Expr_isApp(v___x_2188_);
if (v___x_2189_ == 0)
{
lean_dec_ref(v___x_2188_);
lean_dec(v_goal_2152_);
goto v___jp_2169_;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v___x_2190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2188_);
v___x_2191_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_2192_ = l_Lean_Expr_isConstOf(v___x_2190_, v___x_2191_);
lean_dec_ref(v___x_2190_);
if (v___x_2192_ == 0)
{
lean_dec(v_goal_2152_);
goto v___jp_2169_;
}
else
{
lean_object* v_backwardRules_2193_; lean_object* v_ofPropMeetPreIntro_2194_; lean_object* v___x_2195_; 
v_backwardRules_2193_ = lean_ctor_get(v_a_2154_, 0);
v_ofPropMeetPreIntro_2194_ = lean_ctor_get(v_backwardRules_2193_, 4);
lean_inc_ref(v_ofPropMeetPreIntro_2194_);
v___x_2195_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_ofPropMeetPreIntro_2194_, v_goal_2152_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2204_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2204_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v_a_2196_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2200_);
v___x_2202_ = v___x_2198_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2200_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
v_a_2205_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2195_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2195_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
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
v___jp_2166_:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
v___jp_2169_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_box(0);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropMeetPreIntro_x3f___boxed(lean_object* v_goal_2213_, lean_object* v_pre_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropMeetPreIntro_x3f(v_goal_2213_, v_pre_2214_, v_a_2215_, v_a_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
lean_dec(v_a_2225_);
lean_dec_ref(v_a_2224_);
lean_dec(v_a_2223_);
lean_dec_ref(v_a_2222_);
lean_dec(v_a_2221_);
lean_dec_ref(v_a_2220_);
lean_dec(v_a_2219_);
lean_dec_ref(v_a_2218_);
lean_dec(v_a_2217_);
lean_dec(v_a_2216_);
lean_dec_ref(v_a_2215_);
return v_res_2227_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__3(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2234_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__2));
v___x_2235_ = l_Lean_stringToMessageData(v___x_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f(lean_object* v_goal_2236_, lean_object* v_pre_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; uint8_t v___x_2252_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__1));
v___x_2251_ = lean_unsigned_to_nat(4u);
v___x_2252_ = l_Lean_Expr_isAppOfArity(v_pre_2237_, v___x_2250_, v___x_2251_);
if (v___x_2252_ == 0)
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
lean_dec(v_goal_2236_);
v___x_2253_ = lean_box(0);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
else
{
lean_object* v_backwardRules_2255_; lean_object* v_iSupPreIntro_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_backwardRules_2255_ = lean_ctor_get(v_a_2238_, 0);
v_iSupPreIntro_2256_ = lean_ctor_get(v_backwardRules_2255_, 5);
v___x_2257_ = lean_box(0);
lean_inc(v_goal_2236_);
lean_inc_ref(v_iSupPreIntro_2256_);
v___x_2258_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_iSupPreIntro_2256_, v_goal_2236_, v___x_2257_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2285_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2285_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2285_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; 
if (lean_obj_tag(v_a_2259_) == 1)
{
lean_object* v_mvarIds_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2284_; 
v_mvarIds_2272_ = lean_ctor_get(v_a_2259_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v_a_2259_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2274_ = v_a_2259_;
v_isShared_2275_ = v_isSharedCheck_2284_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_mvarIds_2272_);
lean_dec(v_a_2259_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2284_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
if (lean_obj_tag(v_mvarIds_2272_) == 1)
{
lean_object* v_tail_2276_; 
v_tail_2276_ = lean_ctor_get(v_mvarIds_2272_, 1);
if (lean_obj_tag(v_tail_2276_) == 0)
{
lean_object* v_head_2277_; lean_object* v___x_2279_; 
lean_dec(v_goal_2236_);
v_head_2277_ = lean_ctor_get(v_mvarIds_2272_, 0);
lean_inc(v_head_2277_);
lean_dec_ref_known(v_mvarIds_2272_, 2);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v_head_2277_);
v___x_2279_ = v___x_2274_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_head_2277_);
v___x_2279_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
lean_object* v___x_2281_; 
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2279_);
v___x_2281_ = v___x_2261_;
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
lean_dec_ref_known(v_mvarIds_2272_, 2);
lean_del_object(v___x_2274_);
lean_del_object(v___x_2261_);
v___y_2264_ = v_a_2245_;
v___y_2265_ = v_a_2246_;
v___y_2266_ = v_a_2247_;
v___y_2267_ = v_a_2248_;
goto v___jp_2263_;
}
}
else
{
lean_del_object(v___x_2274_);
lean_dec(v_mvarIds_2272_);
lean_del_object(v___x_2261_);
v___y_2264_ = v_a_2245_;
v___y_2265_ = v_a_2246_;
v___y_2266_ = v_a_2247_;
v___y_2267_ = v_a_2248_;
goto v___jp_2263_;
}
}
}
else
{
lean_del_object(v___x_2261_);
lean_dec(v_a_2259_);
v___y_2264_ = v_a_2245_;
v___y_2265_ = v_a_2246_;
v___y_2266_ = v_a_2247_;
v___y_2267_ = v_a_2248_;
goto v___jp_2263_;
}
v___jp_2263_:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2268_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___closed__3);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_goal_2236_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2270_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2271_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_goal_2236_);
v_a_2286_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2258_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2258_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f___boxed(lean_object* v_goal_2294_, lean_object* v_pre_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f(v_goal_2294_, v_pre_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
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
lean_dec_ref(v_pre_2295_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(lean_object* v_goal_2309_, lean_object* v_00_u03b1_2310_, lean_object* v_pre_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
uint8_t v___x_2324_; 
v___x_2324_ = l_Lean_Expr_isProp(v_00_u03b1_2310_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec(v_goal_2309_);
v___x_2325_ = lean_box(0);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_2328_ = l_Lean_Expr_isAppOf(v_pre_2311_, v___x_2327_);
if (v___x_2328_ == 0)
{
lean_object* v_backwardRules_2329_; lean_object* v_propPreIntro_2330_; lean_object* v___x_2331_; 
v_backwardRules_2329_ = lean_ctor_get(v_a_2312_, 0);
v_propPreIntro_2330_ = lean_ctor_get(v_backwardRules_2329_, 2);
lean_inc_ref(v_propPreIntro_2330_);
v___x_2331_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_propPreIntro_2330_, v_goal_2309_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2336_; lean_object* v___x_2338_; 
v___x_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_a_2332_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v___x_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2331_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2331_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_dec(v_goal_2309_);
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
return v___x_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_2351_, lean_object* v_00_u03b1_2352_, lean_object* v_pre_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_2351_, v_00_u03b1_2352_, v_pre_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
lean_dec(v_a_2364_);
lean_dec_ref(v_a_2363_);
lean_dec(v_a_2362_);
lean_dec_ref(v_a_2361_);
lean_dec(v_a_2360_);
lean_dec_ref(v_a_2359_);
lean_dec(v_a_2358_);
lean_dec_ref(v_a_2357_);
lean_dec(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec_ref(v_pre_2353_);
lean_dec_ref(v_00_u03b1_2352_);
return v_res_2366_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0));
v___x_2369_ = l_Lean_stringToMessageData(v___x_2368_);
return v___x_2369_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = 0;
v___x_2376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3));
v___x_2377_ = l_Lean_MessageData_ofConstName(v___x_2376_, v___x_2375_);
return v___x_2377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2378_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4);
v___x_2379_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1);
v___x_2380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___x_2378_);
return v___x_2380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6));
v___x_2383_ = l_Lean_stringToMessageData(v___x_2382_);
return v___x_2383_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7);
v___x_2385_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5);
v___x_2386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v___x_2384_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(lean_object* v_goal_2387_, lean_object* v_pre_2388_, lean_object* v_target_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; uint8_t v___x_2440_; 
lean_inc_ref(v_pre_2388_);
v___x_2440_ = l_Lean_Expr_isTrue(v_pre_2388_);
if (v___x_2440_ == 0)
{
v___y_2403_ = v_a_2395_;
v___y_2404_ = v_a_2396_;
v___y_2405_ = v_a_2397_;
v___y_2406_ = v_a_2398_;
v___y_2407_ = v_a_2399_;
v___y_2408_ = v_a_2400_;
goto v___jp_2402_;
}
else
{
lean_object* v_backwardRules_2441_; lean_object* v_truePreIntro_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
lean_dec_ref(v_pre_2388_);
v_backwardRules_2441_ = lean_ctor_get(v_a_2390_, 0);
v_truePreIntro_2442_ = lean_ctor_get(v_backwardRules_2441_, 6);
v___x_2443_ = lean_box(0);
lean_inc_ref(v_truePreIntro_2442_);
v___x_2444_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_2442_, v_goal_2387_, v___x_2443_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2480_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2480_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2480_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___y_2450_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; 
if (lean_obj_tag(v_a_2445_) == 1)
{
lean_object* v_mvarIds_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2479_; 
v_mvarIds_2468_ = lean_ctor_get(v_a_2445_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_a_2445_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2470_ = v_a_2445_;
v_isShared_2471_ = v_isSharedCheck_2479_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_mvarIds_2468_);
lean_dec(v_a_2445_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2479_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
if (lean_obj_tag(v_mvarIds_2468_) == 1)
{
lean_object* v_tail_2472_; 
v_tail_2472_ = lean_ctor_get(v_mvarIds_2468_, 1);
if (lean_obj_tag(v_tail_2472_) == 0)
{
lean_object* v___x_2474_; 
lean_dec_ref(v_target_2389_);
if (v_isShared_2471_ == 0)
{
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_mvarIds_2468_);
v___x_2474_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2476_; 
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2474_);
v___x_2476_ = v___x_2447_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2468_, 2);
lean_del_object(v___x_2470_);
lean_del_object(v___x_2447_);
v___y_2450_ = v_a_2395_;
v___y_2451_ = v_a_2396_;
v___y_2452_ = v_a_2397_;
v___y_2453_ = v_a_2398_;
v___y_2454_ = v_a_2399_;
v___y_2455_ = v_a_2400_;
goto v___jp_2449_;
}
}
else
{
lean_del_object(v___x_2470_);
lean_dec(v_mvarIds_2468_);
lean_del_object(v___x_2447_);
v___y_2450_ = v_a_2395_;
v___y_2451_ = v_a_2396_;
v___y_2452_ = v_a_2397_;
v___y_2453_ = v_a_2398_;
v___y_2454_ = v_a_2399_;
v___y_2455_ = v_a_2400_;
goto v___jp_2449_;
}
}
}
else
{
lean_del_object(v___x_2447_);
lean_dec(v_a_2445_);
v___y_2450_ = v_a_2395_;
v___y_2451_ = v_a_2396_;
v___y_2452_ = v_a_2397_;
v___y_2453_ = v_a_2398_;
v___y_2454_ = v_a_2399_;
v___y_2455_ = v_a_2400_;
goto v___jp_2449_;
}
v___jp_2449_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v___x_2456_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8);
v___x_2457_ = l_Lean_indentExpr(v_target_2389_);
v___x_2458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2456_);
lean_ctor_set(v___x_2458_, 1, v___x_2457_);
v___x_2459_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2458_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2459_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2459_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_target_2389_);
v_a_2481_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2444_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2444_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
v___jp_2402_:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(v_goal_2387_, v_target_2389_, v_pre_2388_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2431_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2412_ = v___x_2409_;
v_isShared_2413_ = v_isSharedCheck_2431_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_a_2410_);
lean_dec(v___x_2409_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2431_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
if (lean_obj_tag(v_a_2410_) == 1)
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2426_; 
v_val_2414_ = lean_ctor_get(v_a_2410_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_a_2410_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2416_ = v_a_2410_;
v_isShared_2417_ = v_isSharedCheck_2426_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v_a_2410_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2426_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2421_; 
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2419_, 0, v_val_2414_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v___x_2419_);
v___x_2421_ = v___x_2416_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2419_);
v___x_2421_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
lean_object* v___x_2423_; 
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2421_);
v___x_2423_ = v___x_2412_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v___x_2421_);
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
else
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
lean_dec(v_a_2410_);
v___x_2427_ = lean_box(0);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 0, v___x_2427_);
v___x_2429_ = v___x_2412_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
v_a_2432_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2409_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2409_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_2489_, lean_object* v_pre_2490_, lean_object* v_target_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2489_, v_pre_2490_, v_target_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
lean_dec(v_a_2500_);
lean_dec_ref(v_a_2499_);
lean_dec(v_a_2498_);
lean_dec_ref(v_a_2497_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec(v_a_2493_);
lean_dec_ref(v_a_2492_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object* v_scope_2505_, lean_object* v_goal_2506_, lean_object* v_00_u03b1_2507_, lean_object* v_pre_2508_, lean_object* v_target_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_g_2523_; lean_object* v_g_2530_; lean_object* v_h_2531_; lean_object* v___x_2549_; 
lean_inc_ref(v_pre_2508_);
lean_inc(v_goal_2506_);
v___x_2549_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_2506_, v_pre_2508_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
if (lean_obj_tag(v_a_2550_) == 1)
{
lean_object* v_val_2551_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
v_val_2551_ = lean_ctor_get(v_a_2550_, 0);
lean_inc(v_val_2551_);
lean_dec_ref_known(v_a_2550_, 1);
v_g_2523_ = v_val_2551_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2552_; 
lean_dec(v_a_2550_);
lean_inc_ref(v_pre_2508_);
lean_inc(v_goal_2506_);
v___x_2552_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_2506_, v_pre_2508_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
if (lean_obj_tag(v_a_2553_) == 1)
{
lean_object* v_val_2554_; lean_object* v_fst_2555_; lean_object* v_snd_2556_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
v_val_2554_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v_a_2553_, 1);
v_fst_2555_ = lean_ctor_get(v_val_2554_, 0);
lean_inc(v_fst_2555_);
v_snd_2556_ = lean_ctor_get(v_val_2554_, 1);
lean_inc(v_snd_2556_);
lean_dec(v_val_2554_);
v_g_2530_ = v_fst_2555_;
v_h_2531_ = v_snd_2556_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2557_; 
lean_dec(v_a_2553_);
lean_inc_ref(v_pre_2508_);
lean_inc(v_goal_2506_);
v___x_2557_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropMeetPreIntro_x3f(v_goal_2506_, v_pre_2508_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
if (lean_obj_tag(v_a_2558_) == 1)
{
lean_object* v_val_2559_; lean_object* v_fst_2560_; lean_object* v_snd_2561_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
v_val_2559_ = lean_ctor_get(v_a_2558_, 0);
lean_inc(v_val_2559_);
lean_dec_ref_known(v_a_2558_, 1);
v_fst_2560_ = lean_ctor_get(v_val_2559_, 0);
lean_inc(v_fst_2560_);
v_snd_2561_ = lean_ctor_get(v_val_2559_, 1);
lean_inc(v_snd_2561_);
lean_dec(v_val_2559_);
v_g_2530_ = v_fst_2560_;
v_h_2531_ = v_snd_2561_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2562_; 
lean_dec(v_a_2558_);
lean_inc(v_goal_2506_);
v___x_2562_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_iSupPreIntro_x3f(v_goal_2506_, v_pre_2508_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2562_) == 0)
{
lean_object* v_a_2563_; 
v_a_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_a_2563_);
lean_dec_ref_known(v___x_2562_, 1);
if (lean_obj_tag(v_a_2563_) == 1)
{
lean_object* v_val_2564_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
v_val_2564_ = lean_ctor_get(v_a_2563_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v_a_2563_, 1);
v_g_2523_ = v_val_2564_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2565_; 
lean_dec(v_a_2563_);
lean_inc(v_goal_2506_);
v___x_2565_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_2506_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
if (lean_obj_tag(v_a_2566_) == 1)
{
lean_object* v_val_2567_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
v_val_2567_ = lean_ctor_get(v_a_2566_, 0);
lean_inc(v_val_2567_);
lean_dec_ref_known(v_a_2566_, 1);
v_g_2523_ = v_val_2567_;
goto v___jp_2522_;
}
else
{
lean_object* v___x_2568_; 
lean_dec(v_a_2566_);
lean_inc_ref(v_pre_2508_);
lean_inc(v_goal_2506_);
v___x_2568_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2506_, v_pre_2508_, v_target_2509_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2606_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2606_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2606_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
if (lean_obj_tag(v_a_2569_) == 1)
{
lean_object* v_val_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
v_val_2573_ = lean_ctor_get(v_a_2569_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_a_2569_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2575_ = v_a_2569_;
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_val_2573_);
lean_dec(v_a_2569_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v_scope_2505_);
lean_ctor_set(v___x_2577_, 1, v_val_2573_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 0, v___x_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 0, v___x_2579_);
v___x_2581_ = v___x_2571_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
else
{
lean_object* v___x_2585_; 
lean_del_object(v___x_2571_);
lean_dec(v_a_2569_);
v___x_2585_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_2506_, v_00_u03b1_2507_, v_pre_2508_, v_a_2510_, v_a_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec_ref(v_pre_2508_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2597_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2588_ = v___x_2585_;
v_isShared_2589_ = v_isSharedCheck_2597_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2597_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
if (lean_obj_tag(v_a_2586_) == 1)
{
lean_object* v_val_2590_; lean_object* v_fst_2591_; lean_object* v_snd_2592_; 
lean_del_object(v___x_2588_);
v_val_2590_ = lean_ctor_get(v_a_2586_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v_a_2586_, 1);
v_fst_2591_ = lean_ctor_get(v_val_2590_, 0);
lean_inc(v_fst_2591_);
v_snd_2592_ = lean_ctor_get(v_val_2590_, 1);
lean_inc(v_snd_2592_);
lean_dec(v_val_2590_);
v_g_2530_ = v_fst_2591_;
v_h_2531_ = v_snd_2592_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
lean_dec(v_a_2586_);
lean_dec_ref(v_scope_2505_);
v___x_2593_ = lean_box(0);
if (v_isShared_2589_ == 0)
{
lean_ctor_set(v___x_2588_, 0, v___x_2593_);
v___x_2595_ = v___x_2588_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec_ref(v_scope_2505_);
v_a_2598_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2585_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2585_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
lean_dec_ref(v_scope_2505_);
v_a_2607_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2568_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2568_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2612_; 
if (v_isShared_2610_ == 0)
{
v___x_2612_ = v___x_2609_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
lean_dec_ref(v_scope_2505_);
v_a_2615_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2565_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2565_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
lean_dec_ref(v_scope_2505_);
v_a_2623_ = lean_ctor_get(v___x_2562_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2562_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2562_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2562_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
lean_dec_ref(v_scope_2505_);
v_a_2631_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2557_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2557_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2646_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
lean_dec_ref(v_scope_2505_);
v_a_2639_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2641_ = v___x_2552_;
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_a_2639_);
lean_dec(v___x_2552_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2646_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2644_; 
if (v_isShared_2642_ == 0)
{
v___x_2644_ = v___x_2641_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_a_2639_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v_target_2509_);
lean_dec_ref(v_pre_2508_);
lean_dec(v_goal_2506_);
lean_dec_ref(v_scope_2505_);
v_a_2647_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2549_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2549_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
v___jp_2522_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2525_, 0, v_g_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_scope_2505_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
v___jp_2529_:
{
lean_object* v_specs_2532_; lean_object* v_jps_2533_; lean_object* v_nextDeclIdx_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2547_; 
v_specs_2532_ = lean_ctor_get(v_scope_2505_, 0);
v_jps_2533_ = lean_ctor_get(v_scope_2505_, 1);
v_nextDeclIdx_2534_ = lean_ctor_get(v_scope_2505_, 3);
v_isSharedCheck_2547_ = !lean_is_exclusive(v_scope_2505_);
if (v_isSharedCheck_2547_ == 0)
{
lean_object* v_unused_2548_; 
v_unused_2548_ = lean_ctor_get(v_scope_2505_, 2);
lean_dec(v_unused_2548_);
v___x_2536_ = v_scope_2505_;
v_isShared_2537_ = v_isSharedCheck_2547_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_nextDeclIdx_2534_);
lean_inc(v_jps_2533_);
lean_inc(v_specs_2532_);
lean_dec(v_scope_2505_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2547_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_h_2531_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 2, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_specs_2532_);
lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_jps_2533_);
lean_ctor_set(v_reuseFailAlloc_2546_, 2, v___x_2538_);
lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_nextDeclIdx_2534_);
v___x_2540_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_g_2530_);
lean_ctor_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2540_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
v___x_2545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2655_ = _args[0];
lean_object* v_goal_2656_ = _args[1];
lean_object* v_00_u03b1_2657_ = _args[2];
lean_object* v_pre_2658_ = _args[3];
lean_object* v_target_2659_ = _args[4];
lean_object* v_a_2660_ = _args[5];
lean_object* v_a_2661_ = _args[6];
lean_object* v_a_2662_ = _args[7];
lean_object* v_a_2663_ = _args[8];
lean_object* v_a_2664_ = _args[9];
lean_object* v_a_2665_ = _args[10];
lean_object* v_a_2666_ = _args[11];
lean_object* v_a_2667_ = _args[12];
lean_object* v_a_2668_ = _args[13];
lean_object* v_a_2669_ = _args[14];
lean_object* v_a_2670_ = _args[15];
lean_object* v_a_2671_ = _args[16];
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_2655_, v_goal_2656_, v_00_u03b1_2657_, v_pre_2658_, v_target_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_, v_a_2665_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
lean_dec(v_a_2666_);
lean_dec_ref(v_a_2665_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec_ref(v_00_u03b1_2657_);
return v_res_2672_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0(void){
_start:
{
lean_object* v___x_2673_; lean_object* v_dummy_2674_; 
v___x_2673_ = lean_box(0);
v_dummy_2674_ = l_Lean_Expr_sort___override(v___x_2673_);
return v_dummy_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_2675_, lean_object* v_info_2676_, lean_object* v_prog_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v_head_2690_; lean_object* v_args_2691_; lean_object* v_excessArgs_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_head_2690_ = lean_ctor_get(v_info_2676_, 0);
lean_inc_ref(v_head_2690_);
v_args_2691_ = lean_ctor_get(v_info_2676_, 1);
lean_inc_ref(v_args_2691_);
v_excessArgs_2692_ = lean_ctor_get(v_info_2676_, 2);
lean_inc_ref(v_excessArgs_2692_);
lean_dec_ref(v_info_2676_);
v___x_2693_ = lean_unsigned_to_nat(7u);
v___x_2694_ = lean_array_set(v_args_2691_, v___x_2693_, v_prog_2677_);
v___x_2695_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v_head_2690_, v___x_2694_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec_ref(v___x_2694_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
v___x_2697_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v_a_2696_, v_excessArgs_2692_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec_ref(v_excessArgs_2692_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
lean_inc(v_goal_2675_);
v___x_2699_ = l_Lean_MVarId_getType(v_goal_2675_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; lean_object* v_dummy_2701_; lean_object* v_nargs_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc_n(v_a_2700_, 2);
lean_dec_ref_known(v___x_2699_, 1);
v_dummy_2701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0);
v_nargs_2702_ = l_Lean_Expr_getAppNumArgs(v_a_2700_);
lean_inc(v_nargs_2702_);
v___x_2703_ = lean_mk_array(v_nargs_2702_, v_dummy_2701_);
v___x_2704_ = lean_unsigned_to_nat(1u);
v___x_2705_ = lean_nat_sub(v_nargs_2702_, v___x_2704_);
lean_dec(v_nargs_2702_);
v___x_2706_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2700_, v___x_2703_, v___x_2705_);
v___x_2707_ = l_Lean_Expr_getAppFn(v_a_2700_);
lean_dec(v_a_2700_);
v___x_2708_ = lean_array_get_size(v___x_2706_);
v___x_2709_ = lean_nat_sub(v___x_2708_, v___x_2704_);
v___x_2710_ = lean_array_set(v___x_2706_, v___x_2709_, v_a_2698_);
lean_dec(v___x_2709_);
v___x_2711_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v___x_2707_, v___x_2710_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
lean_dec_ref(v___x_2710_);
if (lean_obj_tag(v___x_2711_) == 0)
{
lean_object* v_a_2712_; lean_object* v___x_2713_; 
v_a_2712_ = lean_ctor_get(v___x_2711_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2711_, 1);
v___x_2713_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2675_, v_a_2712_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_);
return v___x_2713_;
}
else
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2721_; 
lean_dec(v_goal_2675_);
v_a_2714_ = lean_ctor_get(v___x_2711_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v___x_2711_);
if (v_isSharedCheck_2721_ == 0)
{
v___x_2716_ = v___x_2711_;
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2711_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2721_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2719_; 
if (v_isShared_2717_ == 0)
{
v___x_2719_ = v___x_2716_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v_a_2714_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2698_);
lean_dec(v_goal_2675_);
v_a_2722_ = lean_ctor_get(v___x_2699_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2699_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2699_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec(v_goal_2675_);
v_a_2730_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2697_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2697_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
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
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v_excessArgs_2692_);
lean_dec(v_goal_2675_);
v_a_2738_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2695_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2695_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2746_, lean_object* v_info_2747_, lean_object* v_prog_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2746_, v_info_2747_, v_prog_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_, v_a_2759_);
lean_dec(v_a_2759_);
lean_dec_ref(v_a_2758_);
lean_dec(v_a_2757_);
lean_dec_ref(v_a_2756_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
lean_dec(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(lean_object* v_goal_2762_, lean_object* v_info_2763_, lean_object* v_a_2764_, lean_object* v_a_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_2763_);
if (lean_obj_tag(v___x_2776_) == 10)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = l_Lean_Expr_consumeMData(v___x_2776_);
lean_dec_ref_known(v___x_2776_, 2);
v___x_2778_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2762_, v_info_2763_, v___x_2777_, v_a_2764_, v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2787_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2787_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2785_; 
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_a_2779_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2783_);
v___x_2785_ = v___x_2781_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_a_2788_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2778_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2778_);
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
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
lean_dec_ref(v___x_2776_);
lean_dec_ref(v_info_2763_);
lean_dec(v_goal_2762_);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
return v___x_2797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_2798_, lean_object* v_info_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_2798_, v_info_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_);
lean_dec(v_a_2810_);
lean_dec_ref(v_a_2809_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2813_, lean_object* v_start_2814_, lean_object* v_b_2815_, lean_object* v_i_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_nat_dec_le(v_i_2816_, v_start_2814_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v_i_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2825_ = lean_unsigned_to_nat(1u);
v_i_2826_ = lean_nat_sub(v_i_2816_, v___x_2825_);
lean_dec(v_i_2816_);
v___x_2827_ = l_Lean_instInhabitedExpr;
v___x_2828_ = lean_array_get_borrowed(v___x_2827_, v_revArgs_2813_, v_i_2826_);
lean_inc(v___x_2828_);
v___x_2829_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0_spec__0_spec__1___redArg(v_b_2815_, v___x_2828_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v_b_2815_ = v_a_2830_;
v_i_2816_ = v_i_2826_;
goto _start;
}
else
{
lean_dec(v_i_2826_);
return v___x_2829_;
}
}
else
{
lean_object* v___x_2832_; 
lean_dec(v_i_2816_);
v___x_2832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2832_, 0, v_b_2815_);
return v___x_2832_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2833_, lean_object* v_start_2834_, lean_object* v_b_2835_, lean_object* v_i_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2833_, v_start_2834_, v_b_2835_, v_i_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v_start_2834_);
lean_dec_ref(v_revArgs_2833_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2845_, lean_object* v_revArgs_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_unsigned_to_nat(0u);
v___x_2860_ = lean_array_get_size(v_revArgs_2846_);
v___x_2861_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2846_, v___x_2859_, v_f_2845_, v___x_2860_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_2862_, lean_object* v_revArgs_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_f_2862_, v_revArgs_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
lean_dec(v___y_2866_);
lean_dec(v___y_2865_);
lean_dec_ref(v___y_2864_);
lean_dec_ref(v_revArgs_2863_);
return v_res_2876_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0));
v___x_2879_ = l_Lean_stringToMessageData(v___x_2878_);
return v___x_2879_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2));
v___x_2882_ = l_Lean_stringToMessageData(v___x_2881_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object* v_goal_2883_, lean_object* v_info_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_2884_);
v___x_2898_ = l_Lean_Expr_getAppFn(v___x_2897_);
if (lean_obj_tag(v___x_2898_) == 8)
{
lean_object* v_declName_2899_; lean_object* v_type_2900_; lean_object* v_value_2901_; lean_object* v_body_2902_; uint8_t v_nondep_2903_; lean_object* v___x_2904_; 
v_declName_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_n(v_declName_2899_, 2);
v_type_2900_ = lean_ctor_get(v___x_2898_, 1);
lean_inc_ref(v_type_2900_);
v_value_2901_ = lean_ctor_get(v___x_2898_, 2);
lean_inc_ref(v_value_2901_);
v_body_2902_ = lean_ctor_get(v___x_2898_, 3);
lean_inc_ref(v_body_2902_);
v_nondep_2903_ = lean_ctor_get_uint8(v___x_2898_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_2898_, 4);
v___x_2904_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_2899_, v_value_2901_, v_a_2885_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_appArgs_2907_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2914_; lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; uint8_t v___x_2961_; 
lean_dec_ref_known(v___x_2904_, 1);
v___x_2905_ = l_Lean_Expr_getAppNumArgs(v___x_2897_);
v___x_2906_ = lean_mk_empty_array_with_capacity(v___x_2905_);
lean_dec(v___x_2905_);
v_appArgs_2907_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2897_, v___x_2906_);
v___x_2961_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_2901_);
if (v___x_2961_ == 0)
{
lean_object* v_options_2962_; lean_object* v_inheritedTraceOptions_2963_; uint8_t v_hasTrace_2964_; uint8_t v___x_2965_; lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v___y_2970_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; 
v_options_2962_ = lean_ctor_get(v_a_2894_, 2);
v_inheritedTraceOptions_2963_ = lean_ctor_get(v_a_2894_, 13);
v_hasTrace_2964_ = lean_ctor_get_uint8(v_options_2962_, sizeof(void*)*1);
v___x_2965_ = 1;
if (v_hasTrace_2964_ == 0)
{
v___y_2967_ = v_a_2885_;
v___y_2968_ = v_a_2886_;
v___y_2969_ = v_a_2887_;
v___y_2970_ = v_a_2888_;
v___y_2971_ = v_a_2889_;
v___y_2972_ = v_a_2890_;
v___y_2973_ = v_a_2891_;
v___y_2974_ = v_a_2892_;
v___y_2975_ = v_a_2893_;
v___y_2976_ = v_a_2894_;
v___y_2977_ = v_a_2895_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v___x_3076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3077_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3078_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2963_, v_options_2962_, v___x_3077_);
if (v___x_3078_ == 0)
{
v___y_2967_ = v_a_2885_;
v___y_2968_ = v_a_2886_;
v___y_2969_ = v_a_2887_;
v___y_2970_ = v_a_2888_;
v___y_2971_ = v_a_2889_;
v___y_2972_ = v_a_2890_;
v___y_2973_ = v_a_2891_;
v___y_2974_ = v_a_2892_;
v___y_2975_ = v_a_2893_;
v___y_2976_ = v_a_2894_;
v___y_2977_ = v_a_2895_;
goto v___jp_2966_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3079_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_2899_);
v___x_3080_ = l_Lean_MessageData_ofName(v_declName_2899_);
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3079_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3076_, v___x_3081_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_3082_) == 0)
{
lean_dec_ref_known(v___x_3082_, 1);
v___y_2967_ = v_a_2885_;
v___y_2968_ = v_a_2886_;
v___y_2969_ = v_a_2887_;
v___y_2970_ = v_a_2888_;
v___y_2971_ = v_a_2889_;
v___y_2972_ = v_a_2890_;
v___y_2973_ = v_a_2891_;
v___y_2974_ = v_a_2892_;
v___y_2975_ = v_a_2893_;
v___y_2976_ = v_a_2894_;
v___y_2977_ = v_a_2895_;
goto v___jp_2966_;
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v_appArgs_2907_);
lean_dec_ref(v_body_2902_);
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
v___jp_2966_:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_body_2902_, v_appArgs_2907_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v_appArgs_2907_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v_head_2980_; lean_object* v_args_2981_; lean_object* v_excessArgs_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v_head_2980_ = lean_ctor_get(v_info_2884_, 0);
lean_inc_ref(v_head_2980_);
v_args_2981_ = lean_ctor_get(v_info_2884_, 1);
lean_inc_ref(v_args_2981_);
v_excessArgs_2982_ = lean_ctor_get(v_info_2884_, 2);
lean_inc_ref(v_excessArgs_2982_);
lean_dec_ref(v_info_2884_);
v___x_2983_ = lean_unsigned_to_nat(7u);
v___x_2984_ = lean_array_set(v_args_2981_, v___x_2983_, v_a_2979_);
v___x_2985_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v_head_2980_, v___x_2984_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v___x_2984_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v_a_2986_, v_excessArgs_2982_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v_excessArgs_2982_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
lean_inc(v_goal_2883_);
v___x_2989_ = l_Lean_MVarId_getType(v_goal_2883_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v_dummy_2991_; lean_object* v_nargs_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc_n(v_a_2990_, 2);
lean_dec_ref_known(v___x_2989_, 1);
v_dummy_2991_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0);
v_nargs_2992_ = l_Lean_Expr_getAppNumArgs(v_a_2990_);
lean_inc(v_nargs_2992_);
v___x_2993_ = lean_mk_array(v_nargs_2992_, v_dummy_2991_);
v___x_2994_ = lean_unsigned_to_nat(1u);
v___x_2995_ = lean_nat_sub(v_nargs_2992_, v___x_2994_);
lean_dec(v_nargs_2992_);
v___x_2996_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2990_, v___x_2993_, v___x_2995_);
v___x_2997_ = l_Lean_Expr_getAppFn(v_a_2990_);
lean_dec(v_a_2990_);
v___x_2998_ = lean_array_get_size(v___x_2996_);
v___x_2999_ = lean_nat_sub(v___x_2998_, v___x_2994_);
v___x_3000_ = lean_array_set(v___x_2996_, v___x_2999_, v_a_2988_);
lean_dec(v___x_2999_);
v___x_3001_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f_spec__0(v___x_2997_, v___x_3000_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec_ref(v___x_3000_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = l_Lean_Expr_letE___override(v_declName_2899_, v_type_2900_, v_value_2901_, v_a_3002_, v_nondep_2903_);
v___x_3004_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2883_, v___x_3003_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_3007_ = l_Lean_Meta_Sym_intros(v_a_3005_, v___x_3006_, v___x_2965_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3019_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3019_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3019_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
if (lean_obj_tag(v_a_3008_) == 1)
{
lean_object* v_mvarId_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v_mvarId_3012_ = lean_ctor_get(v_a_3008_, 1);
lean_inc(v_mvarId_3012_);
lean_dec_ref_known(v_a_3008_, 2);
v___x_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3013_, 0, v_mvarId_3012_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3013_);
v___x_3015_ = v___x_3010_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
else
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_del_object(v___x_3010_);
lean_dec(v_a_3008_);
v___x_3017_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1);
v___x_3018_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3017_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
return v___x_3018_;
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
v_a_3020_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3007_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3007_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
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
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
v_a_3028_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3004_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3004_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec(v_goal_2883_);
v_a_3036_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3001_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3001_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec(v_a_2988_);
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec(v_goal_2883_);
v_a_3044_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_2989_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_2989_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
else
{
lean_object* v_a_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3059_; 
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec(v_goal_2883_);
v_a_3052_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3059_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3059_ == 0)
{
v___x_3054_ = v___x_2987_;
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_a_3052_);
lean_dec(v___x_2987_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3059_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3057_; 
if (v_isShared_3055_ == 0)
{
v___x_3057_ = v___x_3054_;
goto v_reusejp_3056_;
}
else
{
lean_object* v_reuseFailAlloc_3058_; 
v_reuseFailAlloc_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3052_);
v___x_3057_ = v_reuseFailAlloc_3058_;
goto v_reusejp_3056_;
}
v_reusejp_3056_:
{
return v___x_3057_;
}
}
}
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec_ref(v_excessArgs_2982_);
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec(v_goal_2883_);
v_a_3060_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_2985_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_2985_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
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
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v_a_3068_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_2978_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_2978_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
}
else
{
lean_object* v_options_3091_; uint8_t v_hasTrace_3092_; 
lean_dec_ref(v_type_2900_);
v_options_3091_ = lean_ctor_get(v_a_2894_, 2);
v_hasTrace_3092_ = lean_ctor_get_uint8(v_options_3091_, sizeof(void*)*1);
if (v_hasTrace_3092_ == 0)
{
lean_dec(v_declName_2899_);
v___y_2909_ = v_a_2885_;
v___y_2910_ = v_a_2886_;
v___y_2911_ = v_a_2887_;
v___y_2912_ = v_a_2888_;
v___y_2913_ = v_a_2889_;
v___y_2914_ = v_a_2890_;
v___y_2915_ = v_a_2891_;
v___y_2916_ = v_a_2892_;
v___y_2917_ = v_a_2893_;
v___y_2918_ = v_a_2894_;
v___y_2919_ = v_a_2895_;
goto v___jp_2908_;
}
else
{
lean_object* v_inheritedTraceOptions_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v_inheritedTraceOptions_3093_ = lean_ctor_get(v_a_2894_, 13);
v___x_3094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3095_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3093_, v_options_3091_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_dec(v_declName_2899_);
v___y_2909_ = v_a_2885_;
v___y_2910_ = v_a_2886_;
v___y_2911_ = v_a_2887_;
v___y_2912_ = v_a_2888_;
v___y_2913_ = v_a_2889_;
v___y_2914_ = v_a_2890_;
v___y_2915_ = v_a_2891_;
v___y_2916_ = v_a_2892_;
v___y_2917_ = v_a_2893_;
v___y_2918_ = v_a_2894_;
v___y_2919_ = v_a_2895_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3097_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_3098_ = l_Lean_MessageData_ofName(v_declName_2899_);
v___x_3099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3097_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
v___x_3100_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3094_, v___x_3099_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_dec_ref_known(v___x_3100_, 1);
v___y_2909_ = v_a_2885_;
v___y_2910_ = v_a_2886_;
v___y_2911_ = v_a_2887_;
v___y_2912_ = v_a_2888_;
v___y_2913_ = v_a_2889_;
v___y_2914_ = v_a_2890_;
v___y_2915_ = v_a_2891_;
v___y_2916_ = v_a_2892_;
v___y_2917_ = v_a_2893_;
v___y_2918_ = v_a_2894_;
v___y_2919_ = v_a_2895_;
goto v___jp_2908_;
}
else
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
lean_dec_ref(v_appArgs_2907_);
lean_dec_ref(v_body_2902_);
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v___x_3100_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v___x_3100_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
}
}
}
v___jp_2908_:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2920_ = lean_unsigned_to_nat(1u);
v___x_2921_ = lean_mk_empty_array_with_capacity(v___x_2920_);
v___x_2922_ = lean_array_push(v___x_2921_, v_value_2901_);
v___x_2923_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_2902_, v___x_2922_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; lean_object* v___x_2925_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
v___x_2925_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_a_2924_, v_appArgs_2907_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec_ref(v_appArgs_2907_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2883_, v_info_2884_, v_a_2926_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2936_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2930_ = v___x_2927_;
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2936_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; lean_object* v___x_2934_; 
v___x_2932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2932_, 0, v_a_2928_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2932_);
v___x_2934_ = v___x_2930_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v___x_2932_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
v_a_2937_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2927_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2927_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v_a_2945_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2925_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2925_);
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
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref(v_appArgs_2907_);
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v_a_2953_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2923_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2923_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
lean_dec_ref(v_body_2902_);
lean_dec_ref(v_value_2901_);
lean_dec_ref(v_type_2900_);
lean_dec(v_declName_2899_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v_a_3109_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v___x_2904_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_2904_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
}
else
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec_ref(v___x_2898_);
lean_dec_ref(v___x_2897_);
lean_dec_ref(v_info_2884_);
lean_dec(v_goal_2883_);
v___x_3117_ = lean_box(0);
v___x_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object* v_goal_3119_, lean_object* v_info_3120_, lean_object* v_a_3121_, lean_object* v_a_3122_, lean_object* v_a_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_3119_, v_info_3120_, v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
lean_dec(v_a_3131_);
lean_dec_ref(v_a_3130_);
lean_dec(v_a_3129_);
lean_dec_ref(v_a_3128_);
lean_dec(v_a_3127_);
lean_dec_ref(v_a_3126_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
lean_dec(v_a_3123_);
lean_dec(v_a_3122_);
lean_dec_ref(v_a_3121_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_3134_, lean_object* v_start_3135_, lean_object* v_b_3136_, lean_object* v_i_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; 
v___x_3150_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_3134_, v_start_3135_, v_b_3136_, v_i_3137_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_3151_, lean_object* v_start_3152_, lean_object* v_b_3153_, lean_object* v_i_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_3151_, v_start_3152_, v_b_3153_, v_i_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v_start_3152_);
lean_dec_ref(v_revArgs_3151_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_3168_, lean_object* v_b_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
if (lean_obj_tag(v_as_x27_3168_) == 0)
{
lean_object* v___x_3179_; 
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v_b_3169_);
return v___x_3179_;
}
else
{
lean_object* v_head_3180_; lean_object* v_tail_3181_; lean_object* v___x_3182_; 
v_head_3180_ = lean_ctor_get(v_as_x27_3168_, 0);
v_tail_3181_ = lean_ctor_get(v_as_x27_3168_, 1);
lean_inc(v_head_3180_);
v___x_3182_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_head_3180_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3182_, 1);
switch(lean_obj_tag(v_a_3183_))
{
case 0:
{
lean_object* v___x_3184_; 
lean_inc(v_head_3180_);
v___x_3184_ = lean_array_push(v_b_3169_, v_head_3180_);
v_as_x27_3168_ = v_tail_3181_;
v_b_3169_ = v___x_3184_;
goto _start;
}
case 1:
{
v_as_x27_3168_ = v_tail_3181_;
goto _start;
}
default: 
{
lean_object* v_mvarId_3187_; lean_object* v___x_3188_; 
v_mvarId_3187_ = lean_ctor_get(v_a_3183_, 0);
lean_inc(v_mvarId_3187_);
lean_dec_ref_known(v_a_3183_, 1);
v___x_3188_ = lean_array_push(v_b_3169_, v_mvarId_3187_);
v_as_x27_3168_ = v_tail_3181_;
v_b_3169_ = v___x_3188_;
goto _start;
}
}
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_b_3169_);
v_a_3190_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3182_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___x_3182_);
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
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_3198_, lean_object* v_b_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3198_, v_b_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v_as_x27_3198_);
return v_res_3209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2));
v___x_3215_ = l_Lean_stringToMessageData(v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object* v_goal_3216_, lean_object* v_info_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3217_);
lean_inc_ref(v___x_3230_);
v___x_3231_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_3230_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3374_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3234_ = v___x_3231_;
v_isShared_3235_ = v_isSharedCheck_3374_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3374_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
if (lean_obj_tag(v_a_3232_) == 1)
{
lean_object* v_val_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3369_; 
lean_del_object(v___x_3234_);
v_val_3236_ = lean_ctor_get(v_a_3232_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_a_3232_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3238_ = v_a_3232_;
v_isShared_3239_ = v_isSharedCheck_3369_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_val_3236_);
lean_dec(v_a_3232_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3369_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; 
if (lean_obj_tag(v_val_3236_) == 2)
{
lean_object* v_keyedConfig_3308_; uint8_t v_trackZetaDelta_3309_; lean_object* v_zetaDeltaSet_3310_; lean_object* v_lctx_3311_; lean_object* v_localInstances_3312_; lean_object* v_defEqCtx_x3f_3313_; lean_object* v_synthPendingDepth_3314_; lean_object* v_customCanUnfoldPredicate_x3f_3315_; uint8_t v_univApprox_3316_; uint8_t v_inTypeClassResolution_3317_; uint8_t v_cacheInferType_3318_; uint8_t v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_keyedConfig_3308_ = lean_ctor_get(v_a_3225_, 0);
v_trackZetaDelta_3309_ = lean_ctor_get_uint8(v_a_3225_, sizeof(void*)*7);
v_zetaDeltaSet_3310_ = lean_ctor_get(v_a_3225_, 1);
v_lctx_3311_ = lean_ctor_get(v_a_3225_, 2);
v_localInstances_3312_ = lean_ctor_get(v_a_3225_, 3);
v_defEqCtx_x3f_3313_ = lean_ctor_get(v_a_3225_, 4);
v_synthPendingDepth_3314_ = lean_ctor_get(v_a_3225_, 5);
v_customCanUnfoldPredicate_x3f_3315_ = lean_ctor_get(v_a_3225_, 6);
v_univApprox_3316_ = lean_ctor_get_uint8(v_a_3225_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3317_ = lean_ctor_get_uint8(v_a_3225_, sizeof(void*)*7 + 2);
v_cacheInferType_3318_ = lean_ctor_get_uint8(v_a_3225_, sizeof(void*)*7 + 3);
v___x_3319_ = 2;
lean_inc_ref(v_keyedConfig_3308_);
v___x_3320_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3319_, v_keyedConfig_3308_);
lean_inc(v_customCanUnfoldPredicate_x3f_3315_);
lean_inc(v_synthPendingDepth_3314_);
lean_inc(v_defEqCtx_x3f_3313_);
lean_inc_ref(v_localInstances_3312_);
lean_inc_ref(v_lctx_3311_);
lean_inc(v_zetaDeltaSet_3310_);
v___x_3321_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
lean_ctor_set(v___x_3321_, 1, v_zetaDeltaSet_3310_);
lean_ctor_set(v___x_3321_, 2, v_lctx_3311_);
lean_ctor_set(v___x_3321_, 3, v_localInstances_3312_);
lean_ctor_set(v___x_3321_, 4, v_defEqCtx_x3f_3313_);
lean_ctor_set(v___x_3321_, 5, v_synthPendingDepth_3314_);
lean_ctor_set(v___x_3321_, 6, v_customCanUnfoldPredicate_x3f_3315_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7, v_trackZetaDelta_3309_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7 + 1, v_univApprox_3316_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3317_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*7 + 3, v_cacheInferType_3318_);
v___x_3322_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_3230_, v___x_3321_, v_a_3226_, v_a_3227_, v_a_3228_);
lean_dec_ref_known(v___x_3321_, 7);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
if (lean_obj_tag(v_a_3323_) == 1)
{
lean_object* v_val_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref_known(v_val_3236_, 1);
lean_del_object(v___x_3238_);
lean_dec_ref(v___x_3230_);
v_val_3324_ = lean_ctor_get(v_a_3323_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_a_3323_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3326_ = v_a_3323_;
v_isShared_3327_ = v_isSharedCheck_3360_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_val_3324_);
lean_dec(v_a_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3360_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; 
v___x_3328_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3324_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v___x_3330_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3216_, v_info_3217_, v_a_3329_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3343_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3333_ = v___x_3330_;
v_isShared_3334_ = v_isSharedCheck_3343_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3330_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3343_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3338_; 
v___x_3335_ = lean_box(0);
v___x_3336_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3336_, 0, v_a_3331_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3336_);
v___x_3338_ = v___x_3326_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3336_);
v___x_3338_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3340_; 
if (v_isShared_3334_ == 0)
{
lean_ctor_set(v___x_3333_, 0, v___x_3338_);
v___x_3340_ = v___x_3333_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3351_; 
lean_del_object(v___x_3326_);
v_a_3344_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3346_ = v___x_3330_;
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3330_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3351_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3349_; 
if (v_isShared_3347_ == 0)
{
v___x_3349_ = v___x_3346_;
goto v_reusejp_3348_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3344_);
v___x_3349_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3348_;
}
v_reusejp_3348_:
{
return v___x_3349_;
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_del_object(v___x_3326_);
lean_dec_ref(v_info_3217_);
lean_dec(v_goal_3216_);
v_a_3352_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3328_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3328_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
}
else
{
lean_dec(v_a_3323_);
v___y_3241_ = v_a_3218_;
v___y_3242_ = v_a_3219_;
v___y_3243_ = v_a_3220_;
v___y_3244_ = v_a_3221_;
v___y_3245_ = v_a_3222_;
v___y_3246_ = v_a_3223_;
v___y_3247_ = v_a_3224_;
v___y_3248_ = v_a_3225_;
v___y_3249_ = v_a_3226_;
v___y_3250_ = v_a_3227_;
v___y_3251_ = v_a_3228_;
goto v___jp_3240_;
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref_known(v_val_3236_, 1);
lean_del_object(v___x_3238_);
lean_dec_ref(v___x_3230_);
lean_dec_ref(v_info_3217_);
lean_dec(v_goal_3216_);
v_a_3361_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3322_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3322_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
v___y_3241_ = v_a_3218_;
v___y_3242_ = v_a_3219_;
v___y_3243_ = v_a_3220_;
v___y_3244_ = v_a_3221_;
v___y_3245_ = v_a_3222_;
v___y_3246_ = v_a_3223_;
v___y_3247_ = v_a_3224_;
v___y_3248_ = v_a_3225_;
v___y_3249_ = v_a_3226_;
v___y_3250_ = v_a_3227_;
v___y_3251_ = v_a_3228_;
goto v___jp_3240_;
}
v___jp_3240_:
{
lean_object* v___x_3252_; 
v___x_3252_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_3236_, v_info_3217_, v___y_3242_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3258_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v___x_3254_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1);
v___x_3255_ = l_Lean_indentExpr(v___x_3230_);
lean_inc_ref(v___x_3255_);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3254_);
lean_ctor_set(v___x_3256_, 1, v___x_3255_);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3256_);
v___x_3258_ = v___x_3238_;
goto v_reusejp_3257_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v___x_3256_);
v___x_3258_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3257_;
}
v_reusejp_3257_:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_3253_, v_goal_3216_, v___x_3258_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
if (lean_obj_tag(v_a_3260_) == 1)
{
lean_object* v_mvarIds_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v___x_3255_);
v_mvarIds_3261_ = lean_ctor_get(v_a_3260_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_a_3260_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3263_ = v_a_3260_;
v_isShared_3264_ = v_isSharedCheck_3287_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_mvarIds_3261_);
lean_dec(v_a_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3287_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3265_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_3266_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_3261_, v___x_3265_, v___y_3241_, v___y_3242_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v_mvarIds_3261_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3278_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3269_ = v___x_3266_;
v_isShared_3270_ = v_isSharedCheck_3278_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3266_);
v___x_3269_ = lean_box(0);
v_isShared_3270_ = v_isSharedCheck_3278_;
goto v_resetjp_3268_;
}
v_resetjp_3268_:
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
v___x_3271_ = lean_array_to_list(v_a_3267_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3271_);
v___x_3273_ = v___x_3263_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3275_; 
if (v_isShared_3270_ == 0)
{
lean_ctor_set(v___x_3269_, 0, v___x_3273_);
v___x_3275_ = v___x_3269_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3276_; 
v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
v___x_3275_ = v_reuseFailAlloc_3276_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
return v___x_3275_;
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_del_object(v___x_3263_);
v_a_3279_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3266_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3266_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
else
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
lean_dec(v_a_3260_);
v___x_3288_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3288_);
lean_ctor_set(v___x_3289_, 1, v___x_3255_);
v___x_3290_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3289_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
return v___x_3290_;
}
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec_ref(v___x_3255_);
v_a_3291_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3259_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3259_);
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
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_del_object(v___x_3238_);
lean_dec_ref(v___x_3230_);
lean_dec(v_goal_3216_);
v_a_3300_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3252_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3252_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3305_; 
if (v_isShared_3303_ == 0)
{
v___x_3305_ = v___x_3302_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_a_3300_);
v___x_3305_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
return v___x_3305_;
}
}
}
}
}
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
lean_dec(v_a_3232_);
lean_dec_ref(v___x_3230_);
lean_dec_ref(v_info_3217_);
lean_dec(v_goal_3216_);
v___x_3370_ = lean_box(0);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3370_);
v___x_3372_ = v___x_3234_;
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
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v___x_3230_);
lean_dec_ref(v_info_3217_);
lean_dec(v_goal_3216_);
v_a_3375_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3231_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3231_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3383_, lean_object* v_info_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_3383_, v_info_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
lean_dec(v_a_3395_);
lean_dec_ref(v_a_3394_);
lean_dec(v_a_3393_);
lean_dec_ref(v_a_3392_);
lean_dec(v_a_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_a_3389_);
lean_dec_ref(v_a_3388_);
lean_dec(v_a_3387_);
lean_dec(v_a_3386_);
lean_dec_ref(v_a_3385_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3398_, lean_object* v_as_x27_3399_, lean_object* v_b_3400_, lean_object* v_a_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3399_, v_b_3400_, v___y_3402_, v___y_3403_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3415_, lean_object* v_as_x27_3416_, lean_object* v_b_3417_, lean_object* v_a_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(v_as_3415_, v_as_x27_3416_, v_b_3417_, v_a_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v_as_x27_3416_);
lean_dec(v_as_3415_);
return v_res_3431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3435_, lean_object* v_info_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___x_3449_; lean_object* v_f_3450_; lean_object* v___x_3451_; 
v___x_3449_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3436_);
v_f_3450_ = l_Lean_Expr_getAppFn(v___x_3449_);
v___x_3451_ = l_Lean_Expr_fvarId_x3f(v_f_3450_);
lean_dec_ref(v_f_3450_);
if (lean_obj_tag(v___x_3451_) == 1)
{
lean_object* v_val_3452_; uint8_t v___x_3453_; lean_object* v___x_3454_; 
v_val_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc_n(v_val_3452_, 2);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = 0;
v___x_3454_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3452_, v___x_3453_, v_a_3444_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3542_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3457_ = v___x_3454_;
v_isShared_3458_ = v_isSharedCheck_3542_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3454_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3542_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
if (lean_obj_tag(v_a_3455_) == 1)
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3537_; 
lean_del_object(v___x_3457_);
v_val_3459_ = lean_ctor_get(v_a_3455_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v_a_3455_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3461_ = v_a_3455_;
v_isShared_3462_ = v_isSharedCheck_3537_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v_a_3455_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3537_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v_options_3509_; uint8_t v_hasTrace_3510_; 
v_options_3509_ = lean_ctor_get(v_a_3446_, 2);
v_hasTrace_3510_ = lean_ctor_get_uint8(v_options_3509_, sizeof(void*)*1);
if (v_hasTrace_3510_ == 0)
{
lean_dec(v_val_3452_);
v___y_3464_ = v_a_3437_;
v___y_3465_ = v_a_3438_;
v___y_3466_ = v_a_3439_;
v___y_3467_ = v_a_3440_;
v___y_3468_ = v_a_3441_;
v___y_3469_ = v_a_3442_;
v___y_3470_ = v_a_3443_;
v___y_3471_ = v_a_3444_;
v___y_3472_ = v_a_3445_;
v___y_3473_ = v_a_3446_;
v___y_3474_ = v_a_3447_;
goto v___jp_3463_;
}
else
{
lean_object* v_inheritedTraceOptions_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; uint8_t v___x_3514_; 
v_inheritedTraceOptions_3511_ = lean_ctor_get(v_a_3446_, 13);
v___x_3512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3514_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3511_, v_options_3509_, v___x_3513_);
if (v___x_3514_ == 0)
{
lean_dec(v_val_3452_);
v___y_3464_ = v_a_3437_;
v___y_3465_ = v_a_3438_;
v___y_3466_ = v_a_3439_;
v___y_3467_ = v_a_3440_;
v___y_3468_ = v_a_3441_;
v___y_3469_ = v_a_3442_;
v___y_3470_ = v_a_3443_;
v___y_3471_ = v_a_3444_;
v___y_3472_ = v_a_3445_;
v___y_3473_ = v_a_3446_;
v___y_3474_ = v_a_3447_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Lean_FVarId_getUserName___redArg(v_val_3452_, v_a_3444_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3515_, 1);
v___x_3517_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3518_ = l_Lean_MessageData_ofName(v_a_3516_);
v___x_3519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3517_);
lean_ctor_set(v___x_3519_, 1, v___x_3518_);
v___x_3520_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3512_, v___x_3519_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_dec_ref_known(v___x_3520_, 1);
v___y_3464_ = v_a_3437_;
v___y_3465_ = v_a_3438_;
v___y_3466_ = v_a_3439_;
v___y_3467_ = v_a_3440_;
v___y_3468_ = v_a_3441_;
v___y_3469_ = v_a_3442_;
v___y_3470_ = v_a_3443_;
v___y_3471_ = v_a_3444_;
v___y_3472_ = v_a_3445_;
v___y_3473_ = v_a_3446_;
v___y_3474_ = v_a_3447_;
goto v___jp_3463_;
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref(v___x_3449_);
lean_dec_ref(v_info_3436_);
lean_dec(v_goal_3435_);
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3520_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3520_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref(v___x_3449_);
lean_dec_ref(v_info_3436_);
lean_dec(v_goal_3435_);
v_a_3529_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3515_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3515_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
v___jp_3463_:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3475_ = l_Lean_Expr_getAppNumArgs(v___x_3449_);
v___x_3476_ = lean_mk_empty_array_with_capacity(v___x_3475_);
lean_dec(v___x_3475_);
v___x_3477_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3449_, v___x_3476_);
v___x_3478_ = l_Lean_Expr_betaRev(v_val_3459_, v___x_3477_, v___x_3453_, v___x_3453_);
lean_dec_ref(v___x_3477_);
v___x_3479_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3478_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3481_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
lean_inc(v_a_3480_);
lean_dec_ref_known(v___x_3479_, 1);
v___x_3481_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3435_, v_info_3436_, v_a_3480_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
if (lean_obj_tag(v___x_3481_) == 0)
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3492_; 
v_a_3482_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3484_ = v___x_3481_;
v_isShared_3485_ = v_isSharedCheck_3492_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3481_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3492_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 0, v_a_3482_);
v___x_3487_ = v___x_3461_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
lean_object* v___x_3489_; 
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v___x_3487_);
v___x_3489_ = v___x_3484_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_del_object(v___x_3461_);
v_a_3493_ = lean_ctor_get(v___x_3481_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3481_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3481_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3481_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_del_object(v___x_3461_);
lean_dec_ref(v_info_3436_);
lean_dec(v_goal_3435_);
v_a_3501_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3479_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3479_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
lean_dec(v_a_3455_);
lean_dec(v_val_3452_);
lean_dec_ref(v___x_3449_);
lean_dec_ref(v_info_3436_);
lean_dec(v_goal_3435_);
v___x_3538_ = lean_box(0);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 0, v___x_3538_);
v___x_3540_ = v___x_3457_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_val_3452_);
lean_dec_ref(v___x_3449_);
lean_dec_ref(v_info_3436_);
lean_dec(v_goal_3435_);
v_a_3543_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3454_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3454_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
else
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
lean_dec(v___x_3451_);
lean_dec_ref(v___x_3449_);
lean_dec_ref(v_info_3436_);
lean_dec(v_goal_3435_);
v___x_3551_ = lean_box(0);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3553_, lean_object* v_info_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_){
_start:
{
lean_object* v_res_3567_; 
v_res_3567_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_3553_, v_info_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3568_, lean_object* v_info_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v___x_3582_; lean_object* v_a_3584_; lean_object* v_f_3645_; 
v___x_3582_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3569_);
v_f_3645_ = l_Lean_Expr_getAppFn(v___x_3582_);
if (lean_obj_tag(v_f_3645_) == 11)
{
lean_object* v_keyedConfig_3646_; uint8_t v_trackZetaDelta_3647_; lean_object* v_zetaDeltaSet_3648_; lean_object* v_lctx_3649_; lean_object* v_localInstances_3650_; lean_object* v_defEqCtx_x3f_3651_; lean_object* v_synthPendingDepth_3652_; lean_object* v_customCanUnfoldPredicate_x3f_3653_; uint8_t v_univApprox_3654_; uint8_t v_inTypeClassResolution_3655_; uint8_t v_cacheInferType_3656_; uint8_t v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v_keyedConfig_3646_ = lean_ctor_get(v_a_3577_, 0);
v_trackZetaDelta_3647_ = lean_ctor_get_uint8(v_a_3577_, sizeof(void*)*7);
v_zetaDeltaSet_3648_ = lean_ctor_get(v_a_3577_, 1);
v_lctx_3649_ = lean_ctor_get(v_a_3577_, 2);
v_localInstances_3650_ = lean_ctor_get(v_a_3577_, 3);
v_defEqCtx_x3f_3651_ = lean_ctor_get(v_a_3577_, 4);
v_synthPendingDepth_3652_ = lean_ctor_get(v_a_3577_, 5);
v_customCanUnfoldPredicate_x3f_3653_ = lean_ctor_get(v_a_3577_, 6);
v_univApprox_3654_ = lean_ctor_get_uint8(v_a_3577_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3655_ = lean_ctor_get_uint8(v_a_3577_, sizeof(void*)*7 + 2);
v_cacheInferType_3656_ = lean_ctor_get_uint8(v_a_3577_, sizeof(void*)*7 + 3);
v___x_3657_ = 3;
lean_inc_ref(v_keyedConfig_3646_);
v___x_3658_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3657_, v_keyedConfig_3646_);
lean_inc(v_customCanUnfoldPredicate_x3f_3653_);
lean_inc(v_synthPendingDepth_3652_);
lean_inc(v_defEqCtx_x3f_3651_);
lean_inc_ref(v_localInstances_3650_);
lean_inc_ref(v_lctx_3649_);
lean_inc(v_zetaDeltaSet_3648_);
v___x_3659_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
lean_ctor_set(v___x_3659_, 1, v_zetaDeltaSet_3648_);
lean_ctor_set(v___x_3659_, 2, v_lctx_3649_);
lean_ctor_set(v___x_3659_, 3, v_localInstances_3650_);
lean_ctor_set(v___x_3659_, 4, v_defEqCtx_x3f_3651_);
lean_ctor_set(v___x_3659_, 5, v_synthPendingDepth_3652_);
lean_ctor_set(v___x_3659_, 6, v_customCanUnfoldPredicate_x3f_3653_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*7, v_trackZetaDelta_3647_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*7 + 1, v_univApprox_3654_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3655_);
lean_ctor_set_uint8(v___x_3659_, sizeof(void*)*7 + 3, v_cacheInferType_3656_);
v___x_3660_ = l_Lean_Meta_reduceProj_x3f(v_f_3645_, v___x_3659_, v_a_3578_, v_a_3579_, v_a_3580_);
lean_dec_ref_known(v___x_3659_, 7);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v_a_3584_ = v_a_3661_;
goto v___jp_3583_;
}
else
{
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3662_; 
v_a_3662_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3660_, 1);
v_a_3584_ = v_a_3662_;
goto v___jp_3583_;
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_dec_ref(v___x_3582_);
lean_dec_ref(v_info_3569_);
lean_dec(v_goal_3568_);
v_a_3663_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3660_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3660_);
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
lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_dec_ref(v_f_3645_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v_info_3569_);
lean_dec(v_goal_3568_);
v___x_3671_ = lean_box(0);
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
return v___x_3672_;
}
v___jp_3583_:
{
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3642_; 
v_val_3585_ = lean_ctor_get(v_a_3584_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3587_ = v_a_3584_;
v_isShared_3588_ = v_isSharedCheck_3642_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_val_3585_);
lean_dec(v_a_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3642_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3585_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3591_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3589_, 1);
v___x_3591_ = l_Lean_Meta_Sym_shareCommon(v_a_3590_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref_known(v___x_3591_, 1);
v___x_3593_ = l_Lean_Expr_getAppNumArgs(v___x_3582_);
v___x_3594_ = lean_mk_empty_array_with_capacity(v___x_3593_);
lean_dec(v___x_3593_);
v___x_3595_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3582_, v___x_3594_);
v___x_3596_ = l_Lean_Meta_Sym_betaRevS(v_a_3592_, v___x_3595_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3598_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___x_3598_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3568_, v_info_3569_, v_a_3597_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3609_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3609_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3609_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 0, v_a_3599_);
v___x_3604_ = v___x_3587_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3604_);
v___x_3606_ = v___x_3601_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_del_object(v___x_3587_);
v_a_3610_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3598_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3598_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_del_object(v___x_3587_);
lean_dec_ref(v_info_3569_);
lean_dec(v_goal_3568_);
v_a_3618_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3596_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3596_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_del_object(v___x_3587_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v_info_3569_);
lean_dec(v_goal_3568_);
v_a_3626_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3591_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3591_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_del_object(v___x_3587_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v_info_3569_);
lean_dec(v_goal_3568_);
v_a_3634_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3589_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3589_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
lean_dec(v_a_3584_);
lean_dec_ref(v___x_3582_);
lean_dec_ref(v_info_3569_);
lean_dec(v_goal_3568_);
v___x_3643_ = lean_box(0);
v___x_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
return v___x_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_3673_, lean_object* v_info_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_){
_start:
{
lean_object* v_res_3687_; 
v_res_3687_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_3673_, v_info_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_);
lean_dec(v_a_3685_);
lean_dec_ref(v_a_3684_);
lean_dec(v_a_3683_);
lean_dec_ref(v_a_3682_);
lean_dec(v_a_3681_);
lean_dec_ref(v_a_3680_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec(v_a_3677_);
lean_dec(v_a_3676_);
lean_dec_ref(v_a_3675_);
return v_res_3687_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
return v___x_3696_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_3700_, lean_object* v_a_3701_){
_start:
{
if (lean_obj_tag(v_a_3700_) == 0)
{
lean_object* v___x_3702_; 
v___x_3702_ = l_List_reverse___redArg(v_a_3701_);
return v___x_3702_;
}
else
{
lean_object* v_head_3703_; lean_object* v_tail_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3732_; 
v_head_3703_ = lean_ctor_get(v_a_3700_, 0);
v_tail_3704_ = lean_ctor_get(v_a_3700_, 1);
v_isSharedCheck_3732_ = !lean_is_exclusive(v_a_3700_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3706_ = v_a_3700_;
v_isShared_3707_ = v_isSharedCheck_3732_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_tail_3704_);
lean_inc(v_head_3703_);
lean_dec(v_a_3700_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3732_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___y_3709_; 
switch(lean_obj_tag(v_head_3703_))
{
case 0:
{
lean_object* v_declName_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_declName_3714_ = lean_ctor_get(v_head_3703_, 0);
lean_inc(v_declName_3714_);
lean_dec_ref_known(v_head_3703_, 1);
v___x_3715_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3716_ = l_Lean_MessageData_ofName(v_declName_3714_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___y_3709_ = v___x_3717_;
goto v___jp_3708_;
}
case 1:
{
lean_object* v_fvarId_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v_fvarId_3718_ = lean_ctor_get(v_head_3703_, 0);
lean_inc(v_fvarId_3718_);
lean_dec_ref_known(v_head_3703_, 1);
v___x_3719_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3720_ = l_Lean_mkFVar(v_fvarId_3718_);
v___x_3721_ = l_Lean_MessageData_ofExpr(v___x_3720_);
v___x_3722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3719_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___y_3709_ = v___x_3722_;
goto v___jp_3708_;
}
default: 
{
lean_object* v_ref_3723_; lean_object* v_proof_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_ref_3723_ = lean_ctor_get(v_head_3703_, 1);
lean_inc(v_ref_3723_);
v_proof_3724_ = lean_ctor_get(v_head_3703_, 2);
lean_inc_ref(v_proof_3724_);
lean_dec_ref_known(v_head_3703_, 3);
v___x_3725_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3726_ = l_Lean_MessageData_ofSyntax(v_ref_3723_);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = l_Lean_MessageData_ofExpr(v_proof_3724_);
v___x_3731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3729_);
lean_ctor_set(v___x_3731_, 1, v___x_3730_);
v___y_3709_ = v___x_3731_;
goto v___jp_3708_;
}
}
v___jp_3708_:
{
lean_object* v___x_3711_; 
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 1, v_a_3701_);
lean_ctor_set(v___x_3706_, 0, v___y_3709_);
v___x_3711_ = v___x_3706_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___y_3709_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v_a_3701_);
v___x_3711_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
v_a_3700_ = v_tail_3704_;
v_a_3701_ = v___x_3711_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_3733_, size_t v_i_3734_, lean_object* v_bs_3735_){
_start:
{
uint8_t v___x_3736_; 
v___x_3736_ = lean_usize_dec_lt(v_i_3734_, v_sz_3733_);
if (v___x_3736_ == 0)
{
return v_bs_3735_;
}
else
{
lean_object* v_v_3737_; lean_object* v_proof_3738_; lean_object* v___x_3739_; lean_object* v_bs_x27_3740_; size_t v___x_3741_; size_t v___x_3742_; lean_object* v___x_3743_; 
v_v_3737_ = lean_array_uget_borrowed(v_bs_3735_, v_i_3734_);
v_proof_3738_ = lean_ctor_get(v_v_3737_, 1);
lean_inc_ref(v_proof_3738_);
v___x_3739_ = lean_unsigned_to_nat(0u);
v_bs_x27_3740_ = lean_array_uset(v_bs_3735_, v_i_3734_, v___x_3739_);
v___x_3741_ = ((size_t)1ULL);
v___x_3742_ = lean_usize_add(v_i_3734_, v___x_3741_);
v___x_3743_ = lean_array_uset(v_bs_x27_3740_, v_i_3734_, v_proof_3738_);
v_i_3734_ = v___x_3742_;
v_bs_3735_ = v___x_3743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_3745_, lean_object* v_i_3746_, lean_object* v_bs_3747_){
_start:
{
size_t v_sz_boxed_3748_; size_t v_i_boxed_3749_; lean_object* v_res_3750_; 
v_sz_boxed_3748_ = lean_unbox_usize(v_sz_3745_);
lean_dec(v_sz_3745_);
v_i_boxed_3749_ = lean_unbox_usize(v_i_3746_);
lean_dec(v_i_3746_);
v_res_3750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_3748_, v_i_boxed_3749_, v_bs_3747_);
return v_res_3750_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_3753_ = l_Lean_stringToMessageData(v___x_3752_);
return v___x_3753_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; 
v___x_3755_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_3756_ = l_Lean_stringToMessageData(v___x_3755_);
return v___x_3756_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_3759_ = l_Lean_stringToMessageData(v___x_3758_);
return v___x_3759_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_3762_ = l_Lean_stringToMessageData(v___x_3761_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_3765_ = l_Lean_stringToMessageData(v___x_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_3766_, lean_object* v_monad_3767_, lean_object* v_thms_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
uint8_t v_errorOnMissingSpec_3775_; 
v_errorOnMissingSpec_3775_ = lean_ctor_get_uint8(v_a_3769_, sizeof(void*)*5 + 2);
if (v_errorOnMissingSpec_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3776_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_3776_, 0, v_prog_3766_);
lean_ctor_set(v___x_3776_, 1, v_monad_3767_);
lean_ctor_set(v___x_3776_, 2, v_thms_3768_);
v___x_3777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3777_);
return v___x_3778_;
}
else
{
lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v___x_3779_ = lean_array_get_size(v_thms_3768_);
v___x_3780_ = lean_unsigned_to_nat(0u);
v___x_3781_ = lean_nat_dec_eq(v___x_3779_, v___x_3780_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; size_t v_sz_3791_; size_t v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3782_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_3783_ = l_Lean_MessageData_ofExpr(v_monad_3767_);
v___x_3784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = l_Lean_MessageData_ofExpr(v_prog_3766_);
v___x_3788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3786_);
lean_ctor_set(v___x_3788_, 1, v___x_3787_);
v___x_3789_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_3790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3788_);
lean_ctor_set(v___x_3790_, 1, v___x_3789_);
v_sz_3791_ = lean_array_size(v_thms_3768_);
v___x_3792_ = ((size_t)0ULL);
v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_3791_, v___x_3792_, v_thms_3768_);
v___x_3794_ = lean_array_to_list(v___x_3793_);
v___x_3795_ = lean_box(0);
v___x_3796_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_3794_, v___x_3795_);
v___x_3797_ = l_Lean_MessageData_ofList(v___x_3796_);
v___x_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3790_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___x_3799_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3800_, 0, v___x_3798_);
lean_ctor_set(v___x_3800_, 1, v___x_3799_);
v___x_3801_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3800_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
return v___x_3801_;
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
lean_dec_ref(v_thms_3768_);
lean_dec_ref(v_monad_3767_);
v___x_3802_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_3803_ = l_Lean_MessageData_ofExpr(v_prog_3766_);
v___x_3804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3804_, 0, v___x_3802_);
lean_ctor_set(v___x_3804_, 1, v___x_3803_);
v___x_3805_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3804_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3806_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_);
return v___x_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_3808_, lean_object* v_monad_3809_, lean_object* v_thms_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_res_3817_; 
v_res_3817_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3808_, v_monad_3809_, v_thms_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_);
lean_dec(v_a_3815_);
lean_dec_ref(v_a_3814_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec_ref(v_a_3811_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_3818_, lean_object* v_monad_3819_, lean_object* v_thms_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3818_, v_monad_3819_, v_thms_3820_, v_a_3821_, v_a_3828_, v_a_3829_, v_a_3830_, v_a_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_3834_, lean_object* v_monad_3835_, lean_object* v_thms_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(v_prog_3834_, v_monad_3835_, v_thms_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule_spec__0(lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
if (lean_obj_tag(v_a_3850_) == 0)
{
lean_object* v___x_3852_; 
v___x_3852_ = l_List_reverse___redArg(v_a_3851_);
return v___x_3852_;
}
else
{
lean_object* v_head_3853_; lean_object* v_tail_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3863_; 
v_head_3853_ = lean_ctor_get(v_a_3850_, 0);
v_tail_3854_ = lean_ctor_get(v_a_3850_, 1);
v_isSharedCheck_3863_ = !lean_is_exclusive(v_a_3850_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3856_ = v_a_3850_;
v_isShared_3857_ = v_isSharedCheck_3863_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_tail_3854_);
lean_inc(v_head_3853_);
lean_dec(v_a_3850_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3863_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3858_; lean_object* v___x_3860_; 
v___x_3858_ = l_Lean_MessageData_ofExpr(v_head_3853_);
if (v_isShared_3857_ == 0)
{
lean_ctor_set(v___x_3856_, 1, v_a_3851_);
lean_ctor_set(v___x_3856_, 0, v___x_3858_);
v___x_3860_ = v___x_3856_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v___x_3858_);
lean_ctor_set(v_reuseFailAlloc_3862_, 1, v_a_3851_);
v___x_3860_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
v_a_3850_ = v_tail_3854_;
v_a_3851_ = v___x_3860_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1(void){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__0));
v___x_3866_ = l_Lean_stringToMessageData(v___x_3865_);
return v___x_3866_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__3(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__2));
v___x_3869_ = l_Lean_stringToMessageData(v___x_3868_);
return v___x_3869_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5(void){
_start:
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__4));
v___x_3872_ = l_Lean_stringToMessageData(v___x_3871_);
return v___x_3872_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7(void){
_start:
{
lean_object* v___x_3874_; lean_object* v___x_3875_; 
v___x_3874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__6));
v___x_3875_ = l_Lean_stringToMessageData(v___x_3874_);
return v___x_3875_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9(void){
_start:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__8));
v___x_3878_ = l_Lean_stringToMessageData(v___x_3877_);
return v___x_3878_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__11(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__10));
v___x_3881_ = l_Lean_stringToMessageData(v___x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule(lean_object* v_scope_3882_, lean_object* v_goal_3883_, lean_object* v_info_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v_specs_3897_; lean_object* v_jps_3898_; lean_object* v_lastLiftedPre_x3f_3899_; lean_object* v_nextDeclIdx_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_4073_; 
v_specs_3897_ = lean_ctor_get(v_scope_3882_, 0);
v_jps_3898_ = lean_ctor_get(v_scope_3882_, 1);
v_lastLiftedPre_x3f_3899_ = lean_ctor_get(v_scope_3882_, 2);
v_nextDeclIdx_3900_ = lean_ctor_get(v_scope_3882_, 3);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_scope_3882_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_3902_ = v_scope_3882_;
v_isShared_3903_ = v_isSharedCheck_4073_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_nextDeclIdx_3900_);
lean_inc(v_lastLiftedPre_x3f_3899_);
lean_inc(v_jps_3898_);
lean_inc(v_specs_3897_);
lean_dec(v_scope_3882_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_4073_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3884_);
lean_inc_ref(v___x_3904_);
v___x_3905_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(v_specs_3897_, v___x_3904_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v_fst_3907_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3905_, 1);
v_fst_3907_ = lean_ctor_get(v_a_3906_, 0);
lean_inc(v_fst_3907_);
if (lean_obj_tag(v_fst_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3933_; 
lean_dec(v_a_3906_);
lean_del_object(v___x_3902_);
lean_dec(v_nextDeclIdx_3900_);
lean_dec(v_lastLiftedPre_x3f_3899_);
lean_dec(v_jps_3898_);
lean_dec(v_goal_3883_);
v_a_3908_ = lean_ctor_get(v_fst_3907_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_fst_3907_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3910_ = v_fst_3907_;
v_isShared_3911_ = v_isSharedCheck_3933_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v_fst_3907_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3933_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_3884_);
lean_dec_ref(v_info_3884_);
v___x_3913_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3904_, v___x_3912_, v_a_3908_, v_a_3885_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3924_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3916_ = v___x_3913_;
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3913_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3924_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3911_ == 0)
{
lean_ctor_set(v___x_3910_, 0, v_a_3914_);
v___x_3919_ = v___x_3910_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
lean_object* v___x_3921_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 0, v___x_3919_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_del_object(v___x_3910_);
v_a_3925_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3913_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3913_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
}
else
{
lean_object* v_snd_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_4063_; 
v_snd_3934_ = lean_ctor_get(v_a_3906_, 1);
v_isSharedCheck_4063_ = !lean_is_exclusive(v_a_3906_);
if (v_isSharedCheck_4063_ == 0)
{
lean_object* v_unused_4064_; 
v_unused_4064_ = lean_ctor_get(v_a_3906_, 0);
lean_dec(v_unused_4064_);
v___x_3936_ = v_a_3906_;
v_isShared_3937_ = v_isSharedCheck_4063_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_snd_3934_);
lean_dec(v_a_3906_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_4063_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_4062_; 
v_a_3938_ = lean_ctor_get(v_fst_3907_, 0);
v_isSharedCheck_4062_ = !lean_is_exclusive(v_fst_3907_);
if (v_isSharedCheck_4062_ == 0)
{
v___x_3940_ = v_fst_3907_;
v_isShared_3941_ = v_isSharedCheck_4062_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v_fst_3907_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_4062_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v_snd_3934_);
v___x_3943_ = v___x_3902_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_snd_3934_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_jps_3898_);
lean_ctor_set(v_reuseFailAlloc_4061_, 2, v_lastLiftedPre_x3f_3899_);
lean_ctor_set(v_reuseFailAlloc_4061_, 3, v_nextDeclIdx_3900_);
v___x_3943_ = v_reuseFailAlloc_4061_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___y_3945_; lean_object* v___x_3994_; 
lean_inc_ref(v_info_3884_);
lean_inc(v_a_3938_);
v___x_3994_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_a_3938_, v_info_3884_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_dec(v_goal_3883_);
v___y_3945_ = v___x_3994_;
goto v___jp_3944_;
}
else
{
lean_object* v_a_3995_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; uint8_t v___y_4028_; uint8_t v___x_4059_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
v___x_4059_ = l_Lean_Exception_isInterrupt(v_a_3995_);
if (v___x_4059_ == 0)
{
uint8_t v___x_4060_; 
lean_inc(v_a_3995_);
v___x_4060_ = l_Lean_Exception_isRuntime(v_a_3995_);
v___y_4028_ = v___x_4060_;
goto v___jp_4027_;
}
else
{
v___y_4028_ = v___x_4059_;
goto v___jp_4027_;
}
v___jp_3996_:
{
lean_object* v_excessArgs_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; 
v_excessArgs_4000_ = lean_ctor_get(v_info_3884_, 2);
lean_inc_ref(v___y_3998_);
v___x_4001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4001_, 0, v___y_3998_);
lean_ctor_set(v___x_4001_, 1, v___y_3999_);
v___x_4002_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1);
v___x_4003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4001_);
lean_ctor_set(v___x_4003_, 1, v___x_4002_);
lean_inc_ref(v___x_3904_);
v___x_4004_ = l_Lean_indentExpr(v___x_3904_);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___x_4006_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__3);
v___x_4007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4005_);
lean_ctor_set(v___x_4007_, 1, v___x_4006_);
v___x_4008_ = l_Lean_Exception_toMessageData(v_a_3995_);
v___x_4009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4007_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5);
v___x_4011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4009_);
lean_ctor_set(v___x_4011_, 1, v___x_4010_);
v___x_4012_ = l_Lean_indentExpr(v___y_3997_);
v___x_4013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4011_);
lean_ctor_set(v___x_4013_, 1, v___x_4012_);
v___x_4014_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_3884_);
v___x_4017_ = l_Lean_indentExpr(v___x_4016_);
v___x_4018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4015_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
v___x_4019_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9);
v___x_4020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4018_);
lean_ctor_set(v___x_4020_, 1, v___x_4019_);
lean_inc_ref(v_excessArgs_4000_);
v___x_4021_ = lean_array_to_list(v_excessArgs_4000_);
v___x_4022_ = lean_box(0);
v___x_4023_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule_spec__0(v___x_4021_, v___x_4022_);
v___x_4024_ = l_Lean_MessageData_ofList(v___x_4023_);
v___x_4025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4020_);
lean_ctor_set(v___x_4025_, 1, v___x_4024_);
v___x_4026_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4025_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
v___y_3945_ = v___x_4026_;
goto v___jp_3944_;
}
v___jp_4027_:
{
if (v___y_4028_ == 0)
{
lean_object* v___x_4029_; 
lean_dec_ref_known(v___x_3994_, 1);
v___x_4029_ = l_Lean_MVarId_getType(v_goal_3883_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v_proof_4031_; lean_object* v___x_4032_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v_proof_4031_ = lean_ctor_get(v_a_3938_, 1);
v___x_4032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__11);
switch(lean_obj_tag(v_proof_4031_))
{
case 0:
{
lean_object* v_declName_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_declName_4033_ = lean_ctor_get(v_proof_4031_, 0);
v___x_4034_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_4033_);
v___x_4035_ = l_Lean_MessageData_ofName(v_declName_4033_);
v___x_4036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4034_);
lean_ctor_set(v___x_4036_, 1, v___x_4035_);
v___y_3997_ = v_a_4030_;
v___y_3998_ = v___x_4032_;
v___y_3999_ = v___x_4036_;
goto v___jp_3996_;
}
case 1:
{
lean_object* v_fvarId_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v_fvarId_4037_ = lean_ctor_get(v_proof_4031_, 0);
v___x_4038_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_4037_);
v___x_4039_ = l_Lean_mkFVar(v_fvarId_4037_);
v___x_4040_ = l_Lean_MessageData_ofExpr(v___x_4039_);
v___x_4041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4038_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
v___y_3997_ = v_a_4030_;
v___y_3998_ = v___x_4032_;
v___y_3999_ = v___x_4041_;
goto v___jp_3996_;
}
default: 
{
lean_object* v_ref_4042_; lean_object* v_proof_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v_ref_4042_ = lean_ctor_get(v_proof_4031_, 1);
v_proof_4043_ = lean_ctor_get(v_proof_4031_, 2);
v___x_4044_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_4042_);
v___x_4045_ = l_Lean_MessageData_ofSyntax(v_ref_4042_);
v___x_4046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4044_);
lean_ctor_set(v___x_4046_, 1, v___x_4045_);
v___x_4047_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4046_);
lean_ctor_set(v___x_4048_, 1, v___x_4047_);
lean_inc_ref(v_proof_4043_);
v___x_4049_ = l_Lean_MessageData_ofExpr(v_proof_4043_);
v___x_4050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4048_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
v___y_3997_ = v_a_4030_;
v___y_3998_ = v___x_4032_;
v___y_3999_ = v___x_4050_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
lean_dec(v_a_3995_);
lean_dec_ref(v___x_3943_);
lean_del_object(v___x_3940_);
lean_dec(v_a_3938_);
lean_del_object(v___x_3936_);
lean_dec_ref(v___x_3904_);
lean_dec_ref(v_info_3884_);
v_a_4051_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4058_ == 0)
{
v___x_4053_ = v___x_4029_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4029_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
}
else
{
lean_dec(v_a_3995_);
lean_dec(v_goal_3883_);
v___y_3945_ = v___x_3994_;
goto v___jp_3944_;
}
}
}
v___jp_3944_:
{
if (lean_obj_tag(v___y_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3985_; 
v_a_3946_ = lean_ctor_get(v___y_3945_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___y_3945_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3948_ = v___y_3945_;
v_isShared_3949_ = v_isSharedCheck_3985_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___y_3945_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3985_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
if (lean_obj_tag(v_a_3946_) == 1)
{
lean_object* v_val_3950_; lean_object* v___x_3952_; 
lean_dec_ref(v___x_3904_);
lean_dec_ref(v_info_3884_);
v_val_3950_ = lean_ctor_get(v_a_3946_, 0);
lean_inc(v_val_3950_);
lean_dec_ref_known(v_a_3946_, 1);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 1, v_val_3950_);
lean_ctor_set(v___x_3936_, 0, v_a_3938_);
v___x_3952_ = v___x_3936_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3938_);
lean_ctor_set(v_reuseFailAlloc_3960_, 1, v_val_3950_);
v___x_3952_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
v___x_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3943_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3953_);
v___x_3955_ = v___x_3940_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3959_; 
v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3953_);
v___x_3955_ = v_reuseFailAlloc_3959_;
goto v_reusejp_3954_;
}
v_reusejp_3954_:
{
lean_object* v___x_3957_; 
if (v_isShared_3949_ == 0)
{
lean_ctor_set(v___x_3948_, 0, v___x_3955_);
v___x_3957_ = v___x_3948_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
lean_del_object(v___x_3948_);
lean_dec(v_a_3946_);
lean_dec_ref(v___x_3943_);
lean_del_object(v___x_3936_);
v___x_3961_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_3884_);
lean_dec_ref(v_info_3884_);
v___x_3962_ = lean_unsigned_to_nat(1u);
v___x_3963_ = lean_mk_empty_array_with_capacity(v___x_3962_);
v___x_3964_ = lean_array_push(v___x_3963_, v_a_3938_);
v___x_3965_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3904_, v___x_3961_, v___x_3964_, v_a_3885_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_3976_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_3976_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_3976_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3971_; 
if (v_isShared_3941_ == 0)
{
lean_ctor_set_tag(v___x_3940_, 0);
lean_ctor_set(v___x_3940_, 0, v_a_3966_);
v___x_3971_ = v___x_3940_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3966_);
v___x_3971_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
lean_object* v___x_3973_; 
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3971_);
v___x_3973_ = v___x_3968_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_del_object(v___x_3940_);
v_a_3977_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3965_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3965_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec_ref(v___x_3943_);
lean_del_object(v___x_3940_);
lean_dec(v_a_3938_);
lean_del_object(v___x_3936_);
lean_dec_ref(v___x_3904_);
lean_dec_ref(v_info_3884_);
v_a_3986_ = lean_ctor_get(v___y_3945_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___y_3945_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___y_3945_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___y_3945_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
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
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___x_3904_);
lean_del_object(v___x_3902_);
lean_dec(v_nextDeclIdx_3900_);
lean_dec(v_lastLiftedPre_x3f_3899_);
lean_dec(v_jps_3898_);
lean_dec_ref(v_info_3884_);
lean_dec(v_goal_3883_);
v_a_4065_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_3905_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_3905_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___boxed(lean_object* v_scope_4074_, lean_object* v_goal_4075_, lean_object* v_info_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule(v_scope_4074_, v_goal_4075_, v_info_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, v_a_4086_, v_a_4087_);
lean_dec(v_a_4087_);
lean_dec_ref(v_a_4086_);
lean_dec(v_a_4085_);
lean_dec_ref(v_a_4084_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
lean_dec(v_a_4079_);
lean_dec(v_a_4078_);
lean_dec_ref(v_a_4077_);
return v_res_4089_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__1(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__0));
v___x_4092_ = l_Lean_stringToMessageData(v___x_4091_);
return v___x_4092_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__3(void){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__2));
v___x_4095_ = l_Lean_stringToMessageData(v___x_4094_);
return v___x_4095_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__5(void){
_start:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; 
v___x_4097_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__4));
v___x_4098_ = l_Lean_stringToMessageData(v___x_4097_);
return v___x_4098_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__7(void){
_start:
{
lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4100_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__6));
v___x_4101_ = l_Lean_stringToMessageData(v___x_4100_);
return v___x_4101_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__9(void){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__8));
v___x_4104_ = l_Lean_stringToMessageData(v___x_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule(lean_object* v_scope_4105_, lean_object* v_goal_4106_, lean_object* v_info_4107_, lean_object* v_thm_4108_, lean_object* v_rule_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_){
_start:
{
lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v_options_4251_; uint8_t v_hasTrace_4252_; 
v_options_4251_ = lean_ctor_get(v_a_4119_, 2);
v_hasTrace_4252_ = lean_ctor_get_uint8(v_options_4251_, sizeof(void*)*1);
if (v_hasTrace_4252_ == 0)
{
v___y_4159_ = v_a_4110_;
v___y_4160_ = v_a_4111_;
v___y_4161_ = v_a_4112_;
v___y_4162_ = v_a_4113_;
v___y_4163_ = v_a_4114_;
v___y_4164_ = v_a_4115_;
v___y_4165_ = v_a_4116_;
v___y_4166_ = v_a_4117_;
v___y_4167_ = v_a_4118_;
v___y_4168_ = v_a_4119_;
v___y_4169_ = v_a_4120_;
goto v___jp_4158_;
}
else
{
lean_object* v_inheritedTraceOptions_4253_; lean_object* v_cls_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; 
v_inheritedTraceOptions_4253_ = lean_ctor_get(v_a_4119_, 13);
v_cls_4254_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4255_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4253_, v_options_4251_, v___x_4255_);
if (v___x_4256_ == 0)
{
v___y_4159_ = v_a_4110_;
v___y_4160_ = v_a_4111_;
v___y_4161_ = v_a_4112_;
v___y_4162_ = v_a_4113_;
v___y_4163_ = v_a_4114_;
v___y_4164_ = v_a_4115_;
v___y_4165_ = v_a_4116_;
v___y_4166_ = v_a_4117_;
v___y_4167_ = v_a_4118_;
v___y_4168_ = v_a_4119_;
v___y_4169_ = v_a_4120_;
goto v___jp_4158_;
}
else
{
lean_object* v_proof_4257_; lean_object* v___x_4258_; lean_object* v___y_4260_; 
v_proof_4257_ = lean_ctor_get(v_thm_4108_, 1);
v___x_4258_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__7);
switch(lean_obj_tag(v_proof_4257_))
{
case 0:
{
lean_object* v_declName_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_declName_4284_ = lean_ctor_get(v_proof_4257_, 0);
v___x_4285_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_4284_);
v___x_4286_ = l_Lean_MessageData_ofName(v_declName_4284_);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___y_4260_ = v___x_4287_;
goto v___jp_4259_;
}
case 1:
{
lean_object* v_fvarId_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; 
v_fvarId_4288_ = lean_ctor_get(v_proof_4257_, 0);
v___x_4289_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_4288_);
v___x_4290_ = l_Lean_mkFVar(v_fvarId_4288_);
v___x_4291_ = l_Lean_MessageData_ofExpr(v___x_4290_);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4289_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___y_4260_ = v___x_4292_;
goto v___jp_4259_;
}
default: 
{
lean_object* v_ref_4293_; lean_object* v_proof_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_ref_4293_ = lean_ctor_get(v_proof_4257_, 1);
v_proof_4294_ = lean_ctor_get(v_proof_4257_, 2);
v___x_4295_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_4293_);
v___x_4296_ = l_Lean_MessageData_ofSyntax(v_ref_4293_);
v___x_4297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4297_, 0, v___x_4295_);
lean_ctor_set(v___x_4297_, 1, v___x_4296_);
v___x_4298_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
lean_inc_ref(v_proof_4294_);
v___x_4300_ = l_Lean_MessageData_ofExpr(v_proof_4294_);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___y_4260_ = v___x_4301_;
goto v___jp_4259_;
}
}
v___jp_4259_:
{
lean_object* v_excessArgs_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; 
v_excessArgs_4261_ = lean_ctor_get(v_info_4107_, 2);
v___x_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4258_);
lean_ctor_set(v___x_4262_, 1, v___y_4260_);
v___x_4263_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_4107_);
v___x_4266_ = l_Lean_MessageData_ofExpr(v___x_4265_);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4264_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__9);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4267_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
lean_inc_ref(v_excessArgs_4261_);
v___x_4270_ = lean_array_to_list(v_excessArgs_4261_);
v___x_4271_ = lean_box(0);
v___x_4272_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule_spec__0(v___x_4270_, v___x_4271_);
v___x_4273_ = l_Lean_MessageData_ofList(v___x_4272_);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4269_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_4254_, v___x_4274_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_dec_ref_known(v___x_4275_, 1);
v___y_4159_ = v_a_4110_;
v___y_4160_ = v_a_4111_;
v___y_4161_ = v_a_4112_;
v___y_4162_ = v_a_4113_;
v___y_4163_ = v_a_4114_;
v___y_4164_ = v_a_4115_;
v___y_4165_ = v_a_4116_;
v___y_4166_ = v_a_4117_;
v___y_4167_ = v_a_4118_;
v___y_4168_ = v_a_4119_;
v___y_4169_ = v_a_4120_;
goto v___jp_4158_;
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec_ref(v_rule_4109_);
lean_dec_ref(v_thm_4108_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
lean_dec_ref(v_scope_4105_);
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
}
v___jp_4122_:
{
lean_object* v_excessArgs_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_excessArgs_4132_ = lean_ctor_get(v_info_4107_, 2);
lean_inc_ref(v_excessArgs_4132_);
lean_inc_ref(v___y_4128_);
v___x_4133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4133_, 0, v___y_4128_);
lean_ctor_set(v___x_4133_, 1, v___y_4131_);
v___x_4134_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__1);
v___x_4135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4133_);
lean_ctor_set(v___x_4135_, 1, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
lean_ctor_set(v___x_4136_, 1, v___y_4127_);
v___x_4137_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__5);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = l_Lean_indentExpr(v___y_4126_);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__7);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_4107_);
lean_dec_ref(v_info_4107_);
v___x_4144_ = l_Lean_indentExpr(v___x_4143_);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4142_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
v___x_4146_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule___closed__9);
v___x_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = lean_array_to_list(v_excessArgs_4132_);
v___x_4149_ = lean_box(0);
v___x_4150_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule_spec__0(v___x_4148_, v___x_4149_);
v___x_4151_ = l_Lean_MessageData_ofList(v___x_4150_);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4147_);
lean_ctor_set(v___x_4152_, 1, v___x_4151_);
v___x_4153_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__1);
v___x_4154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4152_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = l_Lean_indentExpr(v___y_4125_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4156_, v___y_4123_, v___y_4124_, v___y_4130_, v___y_4129_);
return v___x_4157_;
}
v___jp_4158_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4170_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__3);
v___x_4171_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_4107_);
lean_inc_ref(v___x_4171_);
v___x_4172_ = l_Lean_indentExpr(v___x_4171_);
lean_inc_ref(v___x_4172_);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4170_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
v___x_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
lean_inc(v_goal_4106_);
lean_inc_ref(v_rule_4109_);
v___x_4175_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_4109_, v_goal_4106_, v___x_4174_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4242_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4242_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4242_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
if (lean_obj_tag(v_a_4176_) == 1)
{
lean_object* v_mvarIds_4180_; lean_object* v___x_4181_; lean_object* v___x_4183_; 
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4171_);
lean_dec_ref(v_rule_4109_);
lean_dec_ref(v_thm_4108_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
v_mvarIds_4180_ = lean_ctor_get(v_a_4176_, 0);
lean_inc(v_mvarIds_4180_);
lean_dec_ref_known(v_a_4176_, 1);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v_scope_4105_);
lean_ctor_set(v___x_4181_, 1, v_mvarIds_4180_);
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4181_);
v___x_4183_ = v___x_4178_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
else
{
lean_object* v___x_4185_; 
lean_del_object(v___x_4178_);
lean_dec(v_a_4176_);
lean_dec_ref(v_scope_4105_);
lean_inc_ref(v___x_4171_);
lean_inc_ref(v_thm_4108_);
v___x_4185_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorem_patternMatches(v_thm_4108_, v___x_4171_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_object* v_a_4186_; uint8_t v___x_4187_; 
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v___x_4187_ = lean_unbox(v_a_4186_);
lean_dec(v_a_4186_);
if (v___x_4187_ == 0)
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_dec_ref(v___x_4172_);
lean_dec_ref(v_rule_4109_);
lean_dec(v_goal_4106_);
v___x_4188_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_4107_);
lean_dec_ref(v_info_4107_);
v___x_4189_ = lean_unsigned_to_nat(1u);
v___x_4190_ = lean_mk_empty_array_with_capacity(v___x_4189_);
v___x_4191_ = lean_array_push(v___x_4190_, v_thm_4108_);
v___x_4192_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_4171_, v___x_4188_, v___x_4191_, v___y_4159_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
return v___x_4192_;
}
else
{
lean_object* v_expr_4193_; lean_object* v___x_4194_; 
lean_dec_ref(v___x_4171_);
v_expr_4193_ = lean_ctor_get(v_rule_4109_, 0);
lean_inc_ref(v_expr_4193_);
lean_dec_ref(v_rule_4109_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
lean_inc(v___y_4167_);
lean_inc_ref(v___y_4166_);
v___x_4194_ = lean_infer_type(v_expr_4193_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_object* v_a_4195_; lean_object* v___x_4196_; 
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___x_4196_ = l_Lean_MVarId_getType(v_goal_4106_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; lean_object* v_proof_4198_; lean_object* v___x_4199_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v_proof_4198_ = lean_ctor_get(v_thm_4108_, 1);
lean_inc_ref(v_proof_4198_);
lean_dec_ref(v_thm_4108_);
v___x_4199_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___closed__5);
switch(lean_obj_tag(v_proof_4198_))
{
case 0:
{
lean_object* v_declName_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v_declName_4200_ = lean_ctor_get(v_proof_4198_, 0);
lean_inc(v_declName_4200_);
lean_dec_ref_known(v_proof_4198_, 1);
v___x_4201_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_4202_ = l_Lean_MessageData_ofName(v_declName_4200_);
v___x_4203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___y_4123_ = v___y_4166_;
v___y_4124_ = v___y_4167_;
v___y_4125_ = v_a_4195_;
v___y_4126_ = v_a_4197_;
v___y_4127_ = v___x_4172_;
v___y_4128_ = v___x_4199_;
v___y_4129_ = v___y_4169_;
v___y_4130_ = v___y_4168_;
v___y_4131_ = v___x_4203_;
goto v___jp_4122_;
}
case 1:
{
lean_object* v_fvarId_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v_fvarId_4204_ = lean_ctor_get(v_proof_4198_, 0);
lean_inc(v_fvarId_4204_);
lean_dec_ref_known(v_proof_4198_, 1);
v___x_4205_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_4206_ = l_Lean_mkFVar(v_fvarId_4204_);
v___x_4207_ = l_Lean_MessageData_ofExpr(v___x_4206_);
v___x_4208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4205_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___y_4123_ = v___y_4166_;
v___y_4124_ = v___y_4167_;
v___y_4125_ = v_a_4195_;
v___y_4126_ = v_a_4197_;
v___y_4127_ = v___x_4172_;
v___y_4128_ = v___x_4199_;
v___y_4129_ = v___y_4169_;
v___y_4130_ = v___y_4168_;
v___y_4131_ = v___x_4208_;
goto v___jp_4122_;
}
default: 
{
lean_object* v_ref_4209_; lean_object* v_proof_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_ref_4209_ = lean_ctor_get(v_proof_4198_, 1);
lean_inc(v_ref_4209_);
v_proof_4210_ = lean_ctor_get(v_proof_4198_, 2);
lean_inc_ref(v_proof_4210_);
lean_dec_ref_known(v_proof_4198_, 3);
v___x_4211_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_4212_ = l_Lean_MessageData_ofSyntax(v_ref_4209_);
v___x_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = l_Lean_MessageData_ofExpr(v_proof_4210_);
v___x_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___y_4123_ = v___y_4166_;
v___y_4124_ = v___y_4167_;
v___y_4125_ = v_a_4195_;
v___y_4126_ = v_a_4197_;
v___y_4127_ = v___x_4172_;
v___y_4128_ = v___x_4199_;
v___y_4129_ = v___y_4169_;
v___y_4130_ = v___y_4168_;
v___y_4131_ = v___x_4217_;
goto v___jp_4122_;
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec(v_a_4195_);
lean_dec_ref(v___x_4172_);
lean_dec_ref(v_thm_4108_);
lean_dec_ref(v_info_4107_);
v_a_4218_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4196_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4196_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec_ref(v___x_4172_);
lean_dec_ref(v_thm_4108_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
v_a_4226_ = lean_ctor_get(v___x_4194_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4194_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4194_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4194_);
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
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4171_);
lean_dec_ref(v_rule_4109_);
lean_dec_ref(v_thm_4108_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
v_a_4234_ = lean_ctor_get(v___x_4185_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4185_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4185_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4185_);
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
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v___x_4172_);
lean_dec_ref(v___x_4171_);
lean_dec_ref(v_rule_4109_);
lean_dec_ref(v_thm_4108_);
lean_dec_ref(v_info_4107_);
lean_dec(v_goal_4106_);
lean_dec_ref(v_scope_4105_);
v_a_4243_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4175_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4175_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule___boxed(lean_object** _args){
lean_object* v_scope_4302_ = _args[0];
lean_object* v_goal_4303_ = _args[1];
lean_object* v_info_4304_ = _args[2];
lean_object* v_thm_4305_ = _args[3];
lean_object* v_rule_4306_ = _args[4];
lean_object* v_a_4307_ = _args[5];
lean_object* v_a_4308_ = _args[6];
lean_object* v_a_4309_ = _args[7];
lean_object* v_a_4310_ = _args[8];
lean_object* v_a_4311_ = _args[9];
lean_object* v_a_4312_ = _args[10];
lean_object* v_a_4313_ = _args[11];
lean_object* v_a_4314_ = _args[12];
lean_object* v_a_4315_ = _args[13];
lean_object* v_a_4316_ = _args[14];
lean_object* v_a_4317_ = _args[15];
lean_object* v_a_4318_ = _args[16];
_start:
{
lean_object* v_res_4319_; 
v_res_4319_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule(v_scope_4302_, v_goal_4303_, v_info_4304_, v_thm_4305_, v_rule_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_);
lean_dec(v_a_4317_);
lean_dec_ref(v_a_4316_);
lean_dec(v_a_4315_);
lean_dec_ref(v_a_4314_);
lean_dec(v_a_4313_);
lean_dec_ref(v_a_4312_);
lean_dec(v_a_4311_);
lean_dec_ref(v_a_4310_);
lean_dec(v_a_4309_);
lean_dec(v_a_4308_);
lean_dec_ref(v_a_4307_);
return v_res_4319_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_4322_ = l_Lean_stringToMessageData(v___x_4321_);
return v___x_4322_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_4325_ = l_Lean_stringToMessageData(v___x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v_untilPat_x3f_4335_; 
v_untilPat_x3f_4335_ = lean_ctor_get(v_a_4327_, 4);
if (lean_obj_tag(v_untilPat_x3f_4335_) == 1)
{
lean_object* v_val_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; 
v_val_4336_ = lean_ctor_get(v_untilPat_x3f_4335_, 0);
v___x_4337_ = 1;
lean_inc_ref(v_prog_4326_);
lean_inc(v_val_4336_);
v___x_4338_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_4336_, v_prog_4326_, v___x_4337_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
if (lean_obj_tag(v___x_4338_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4385_; 
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4385_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4385_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
if (lean_obj_tag(v_a_4339_) == 0)
{
uint8_t v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
lean_dec_ref(v_prog_4326_);
v___x_4343_ = 0;
v___x_4344_ = lean_box(v___x_4343_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v___x_4344_);
v___x_4346_ = v___x_4341_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4347_; 
v_reuseFailAlloc_4347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4344_);
v___x_4346_ = v_reuseFailAlloc_4347_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
return v___x_4346_;
}
}
else
{
lean_object* v_options_4348_; uint8_t v_hasTrace_4349_; 
lean_dec_ref_known(v_a_4339_, 1);
v_options_4348_ = lean_ctor_get(v_a_4332_, 2);
v_hasTrace_4349_ = lean_ctor_get_uint8(v_options_4348_, sizeof(void*)*1);
if (v_hasTrace_4349_ == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4352_; 
lean_dec_ref(v_prog_4326_);
v___x_4350_ = lean_box(v___x_4337_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v___x_4350_);
v___x_4352_ = v___x_4341_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; uint8_t v___x_4357_; 
v_inheritedTraceOptions_4354_ = lean_ctor_get(v_a_4332_, 13);
v___x_4355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4357_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4354_, v_options_4348_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4360_; 
lean_dec_ref(v_prog_4326_);
v___x_4358_ = lean_box(v___x_4337_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v___x_4358_);
v___x_4360_ = v___x_4341_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
else
{
lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
lean_del_object(v___x_4341_);
v___x_4362_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4363_ = l_Lean_MessageData_ofExpr(v_prog_4326_);
v___x_4364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4362_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
v___x_4365_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4355_, v___x_4366_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4375_; 
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4375_ == 0)
{
lean_object* v_unused_4376_; 
v_unused_4376_ = lean_ctor_get(v___x_4367_, 0);
lean_dec(v_unused_4376_);
v___x_4369_ = v___x_4367_;
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
else
{
lean_dec(v___x_4367_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4375_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4371_ = lean_box(v___x_4337_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 0, v___x_4371_);
v___x_4373_ = v___x_4369_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
v_a_4377_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4367_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4367_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
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
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_dec_ref(v_prog_4326_);
v_a_4386_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4338_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4338_);
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
else
{
uint8_t v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; 
lean_dec_ref(v_prog_4326_);
v___x_4394_ = 0;
v___x_4395_ = lean_box(v___x_4394_);
v___x_4396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4396_, 0, v___x_4395_);
return v___x_4396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4397_, lean_object* v_a_4398_, lean_object* v_a_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_prog_4397_, v_a_4398_, v_a_4399_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_, v_a_4404_);
lean_dec(v_a_4404_);
lean_dec_ref(v_a_4403_);
lean_dec(v_a_4402_);
lean_dec_ref(v_a_4401_);
lean_dec(v_a_4400_);
lean_dec_ref(v_a_4399_);
lean_dec_ref(v_a_4398_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object* v_prog_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v___x_4420_; 
v___x_4420_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_prog_4407_, v_a_4408_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_, v_a_4418_);
return v___x_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_){
_start:
{
lean_object* v_res_4434_; 
v_res_4434_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v_prog_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_);
lean_dec(v_a_4432_);
lean_dec_ref(v_a_4431_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
lean_dec(v_a_4428_);
lean_dec_ref(v_a_4427_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
return v_res_4434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v_b_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___x_4449_; 
lean_inc(v___y_4447_);
lean_inc_ref(v___y_4446_);
lean_inc(v___y_4445_);
lean_inc_ref(v___y_4444_);
lean_inc(v___y_4442_);
lean_inc_ref(v___y_4441_);
lean_inc(v___y_4440_);
lean_inc_ref(v___y_4439_);
lean_inc(v___y_4438_);
lean_inc(v___y_4437_);
lean_inc_ref(v___y_4436_);
v___x_4449_ = lean_apply_13(v_k_4435_, v_b_4443_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, lean_box(0));
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v_b_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v_b_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4465_, lean_object* v_type_4466_, lean_object* v_val_4467_, lean_object* v_k_4468_, uint8_t v_nondep_4469_, uint8_t v_kind_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v___f_4483_; lean_object* v___x_4484_; 
lean_inc(v___y_4477_);
lean_inc_ref(v___y_4476_);
lean_inc(v___y_4475_);
lean_inc_ref(v___y_4474_);
lean_inc(v___y_4473_);
lean_inc(v___y_4472_);
lean_inc_ref(v___y_4471_);
v___f_4483_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4483_, 0, v_k_4468_);
lean_closure_set(v___f_4483_, 1, v___y_4471_);
lean_closure_set(v___f_4483_, 2, v___y_4472_);
lean_closure_set(v___f_4483_, 3, v___y_4473_);
lean_closure_set(v___f_4483_, 4, v___y_4474_);
lean_closure_set(v___f_4483_, 5, v___y_4475_);
lean_closure_set(v___f_4483_, 6, v___y_4476_);
lean_closure_set(v___f_4483_, 7, v___y_4477_);
v___x_4484_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4465_, v_type_4466_, v_val_4467_, v___f_4483_, v_nondep_4469_, v_kind_4470_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
if (lean_obj_tag(v___x_4484_) == 0)
{
return v___x_4484_;
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4484_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4493_ = _args[0];
lean_object* v_type_4494_ = _args[1];
lean_object* v_val_4495_ = _args[2];
lean_object* v_k_4496_ = _args[3];
lean_object* v_nondep_4497_ = _args[4];
lean_object* v_kind_4498_ = _args[5];
lean_object* v___y_4499_ = _args[6];
lean_object* v___y_4500_ = _args[7];
lean_object* v___y_4501_ = _args[8];
lean_object* v___y_4502_ = _args[9];
lean_object* v___y_4503_ = _args[10];
lean_object* v___y_4504_ = _args[11];
lean_object* v___y_4505_ = _args[12];
lean_object* v___y_4506_ = _args[13];
lean_object* v___y_4507_ = _args[14];
lean_object* v___y_4508_ = _args[15];
lean_object* v___y_4509_ = _args[16];
lean_object* v___y_4510_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4511_; uint8_t v_kind_boxed_4512_; lean_object* v_res_4513_; 
v_nondep_boxed_4511_ = lean_unbox(v_nondep_4497_);
v_kind_boxed_4512_ = lean_unbox(v_kind_4498_);
v_res_4513_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4493_, v_type_4494_, v_val_4495_, v_k_4496_, v_nondep_boxed_4511_, v_kind_boxed_4512_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4514_, lean_object* v_name_4515_, lean_object* v_type_4516_, lean_object* v_val_4517_, lean_object* v_k_4518_, uint8_t v_nondep_4519_, uint8_t v_kind_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4515_, v_type_4516_, v_val_4517_, v_k_4518_, v_nondep_4519_, v_kind_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4534_ = _args[0];
lean_object* v_name_4535_ = _args[1];
lean_object* v_type_4536_ = _args[2];
lean_object* v_val_4537_ = _args[3];
lean_object* v_k_4538_ = _args[4];
lean_object* v_nondep_4539_ = _args[5];
lean_object* v_kind_4540_ = _args[6];
lean_object* v___y_4541_ = _args[7];
lean_object* v___y_4542_ = _args[8];
lean_object* v___y_4543_ = _args[9];
lean_object* v___y_4544_ = _args[10];
lean_object* v___y_4545_ = _args[11];
lean_object* v___y_4546_ = _args[12];
lean_object* v___y_4547_ = _args[13];
lean_object* v___y_4548_ = _args[14];
lean_object* v___y_4549_ = _args[15];
lean_object* v___y_4550_ = _args[16];
lean_object* v___y_4551_ = _args[17];
lean_object* v___y_4552_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4553_; uint8_t v_kind_boxed_4554_; lean_object* v_res_4555_; 
v_nondep_boxed_4553_ = lean_unbox(v_nondep_4539_);
v_kind_boxed_4554_ = lean_unbox(v_kind_4540_);
v_res_4555_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4534_, v_name_4535_, v_type_4536_, v_val_4537_, v_k_4538_, v_nondep_boxed_4553_, v_kind_boxed_4554_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4556_, lean_object* v_declInfos_4557_, lean_object* v_k_4558_, lean_object* v_fv_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4556_, v_declInfos_4557_, v_k_4558_, v_fv_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
lean_dec(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec(v___y_4562_);
lean_dec(v___y_4561_);
lean_dec_ref(v___y_4560_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4573_, lean_object* v_k_4574_, lean_object* v_acc_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_, lean_object* v_a_4583_, lean_object* v_a_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_){
_start:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; uint8_t v___x_4590_; 
v___x_4588_ = lean_array_get_size(v_acc_4575_);
v___x_4589_ = lean_array_get_size(v_declInfos_4573_);
v___x_4590_ = lean_nat_dec_lt(v___x_4588_, v___x_4589_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; 
lean_dec_ref(v_declInfos_4573_);
lean_inc(v_a_4586_);
lean_inc_ref(v_a_4585_);
lean_inc(v_a_4584_);
lean_inc_ref(v_a_4583_);
lean_inc(v_a_4582_);
lean_inc_ref(v_a_4581_);
lean_inc(v_a_4580_);
lean_inc_ref(v_a_4579_);
lean_inc(v_a_4578_);
lean_inc(v_a_4577_);
lean_inc_ref(v_a_4576_);
v___x_4591_ = lean_apply_13(v_k_4574_, v_acc_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_, lean_box(0));
return v___x_4591_;
}
else
{
lean_object* v___x_4592_; lean_object* v_snd_4593_; lean_object* v_fst_4594_; lean_object* v_fst_4595_; lean_object* v_snd_4596_; lean_object* v___f_4597_; uint8_t v___x_4598_; uint8_t v___x_4599_; lean_object* v___x_4600_; 
v___x_4592_ = lean_array_fget_borrowed(v_declInfos_4573_, v___x_4588_);
v_snd_4593_ = lean_ctor_get(v___x_4592_, 1);
v_fst_4594_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_fst_4594_);
v_fst_4595_ = lean_ctor_get(v_snd_4593_, 0);
lean_inc(v_fst_4595_);
v_snd_4596_ = lean_ctor_get(v_snd_4593_, 1);
lean_inc(v_snd_4596_);
v___f_4597_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4597_, 0, v_acc_4575_);
lean_closure_set(v___f_4597_, 1, v_declInfos_4573_);
lean_closure_set(v___f_4597_, 2, v_k_4574_);
v___x_4598_ = 0;
v___x_4599_ = 0;
v___x_4600_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4594_, v_fst_4595_, v_snd_4596_, v___f_4597_, v___x_4598_, v___x_4599_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_, v_a_4582_, v_a_4583_, v_a_4584_, v_a_4585_, v_a_4586_);
return v___x_4600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4601_, lean_object* v_declInfos_4602_, lean_object* v_k_4603_, lean_object* v_fv_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = lean_array_push(v_acc_4601_, v_fv_4604_);
v___x_4618_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4602_, v_k_4603_, v___x_4617_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4619_, lean_object* v_k_4620_, lean_object* v_acc_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_, lean_object* v_a_4625_, lean_object* v_a_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4619_, v_k_4620_, v_acc_4621_, v_a_4622_, v_a_4623_, v_a_4624_, v_a_4625_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
lean_dec(v_a_4626_);
lean_dec_ref(v_a_4625_);
lean_dec(v_a_4624_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4635_, lean_object* v_h__1_4636_){
_start:
{
lean_object* v_snd_4637_; lean_object* v_fst_4638_; lean_object* v_fst_4639_; lean_object* v_snd_4640_; lean_object* v___x_4641_; 
v_snd_4637_ = lean_ctor_get(v_x_4635_, 1);
lean_inc(v_snd_4637_);
v_fst_4638_ = lean_ctor_get(v_x_4635_, 0);
lean_inc(v_fst_4638_);
lean_dec_ref(v_x_4635_);
v_fst_4639_ = lean_ctor_get(v_snd_4637_, 0);
lean_inc(v_fst_4639_);
v_snd_4640_ = lean_ctor_get(v_snd_4637_, 1);
lean_inc(v_snd_4640_);
lean_dec(v_snd_4637_);
v___x_4641_ = lean_apply_3(v_h__1_4636_, v_fst_4638_, v_fst_4639_, v_snd_4640_);
return v___x_4641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4642_, lean_object* v_x_4643_, lean_object* v_h__1_4644_){
_start:
{
lean_object* v_snd_4645_; lean_object* v_fst_4646_; lean_object* v_fst_4647_; lean_object* v_snd_4648_; lean_object* v___x_4649_; 
v_snd_4645_ = lean_ctor_get(v_x_4643_, 1);
lean_inc(v_snd_4645_);
v_fst_4646_ = lean_ctor_get(v_x_4643_, 0);
lean_inc(v_fst_4646_);
lean_dec_ref(v_x_4643_);
v_fst_4647_ = lean_ctor_get(v_snd_4645_, 0);
lean_inc(v_fst_4647_);
v_snd_4648_ = lean_ctor_get(v_snd_4645_, 1);
lean_inc(v_snd_4648_);
lean_dec(v_snd_4645_);
v___x_4649_ = lean_apply_3(v_h__1_4644_, v_fst_4646_, v_fst_4647_, v_snd_4648_);
return v___x_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(lean_object* v_declInfos_4652_, lean_object* v_k_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_){
_start:
{
lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0));
v___x_4667_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4652_, v_k_4653_, v___x_4666_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_, v_a_4664_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4668_, lean_object* v_k_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_, lean_object* v_a_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(v_declInfos_4668_, v_k_4669_, v_a_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_, v_a_4675_, v_a_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
lean_dec(v_a_4680_);
lean_dec_ref(v_a_4679_);
lean_dec(v_a_4678_);
lean_dec_ref(v_a_4677_);
lean_dec(v_a_4676_);
lean_dec_ref(v_a_4675_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec(v_a_4671_);
lean_dec_ref(v_a_4670_);
return v_res_4682_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object* v_x_4683_){
_start:
{
uint8_t v___x_4684_; 
v___x_4684_ = 0;
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4685_){
_start:
{
uint8_t v_res_4686_; lean_object* v_r_4687_; 
v_res_4686_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(v_x_4685_);
lean_dec(v_x_4685_);
v_r_4687_ = lean_box(v_res_4686_);
return v_r_4687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4688_, lean_object* v___x_4689_, uint8_t v___x_4690_, lean_object* v___x_4691_, lean_object* v_fvs_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_){
_start:
{
lean_object* v___x_4700_; 
v___x_4700_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4688_, v___x_4689_, v___x_4690_, v___x_4690_, v___x_4691_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
v___x_4702_ = 0;
v___x_4703_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4702_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
if (lean_obj_tag(v___x_4703_) == 0)
{
uint8_t v___x_4704_; lean_object* v___x_4705_; 
lean_dec_ref_known(v___x_4703_, 1);
v___x_4704_ = 1;
v___x_4705_ = l_Lean_Meta_mkLetFVars(v_fvs_4692_, v_a_4701_, v___x_4690_, v___x_4690_, v___x_4704_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
return v___x_4705_;
}
else
{
lean_object* v_a_4706_; lean_object* v___x_4708_; uint8_t v_isShared_4709_; uint8_t v_isSharedCheck_4713_; 
lean_dec(v_a_4701_);
v_a_4706_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4713_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4713_ == 0)
{
v___x_4708_ = v___x_4703_;
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
else
{
lean_inc(v_a_4706_);
lean_dec(v___x_4703_);
v___x_4708_ = lean_box(0);
v_isShared_4709_ = v_isSharedCheck_4713_;
goto v_resetjp_4707_;
}
v_resetjp_4707_:
{
lean_object* v___x_4711_; 
if (v_isShared_4709_ == 0)
{
v___x_4711_ = v___x_4708_;
goto v_reusejp_4710_;
}
else
{
lean_object* v_reuseFailAlloc_4712_; 
v_reuseFailAlloc_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4712_, 0, v_a_4706_);
v___x_4711_ = v_reuseFailAlloc_4712_;
goto v_reusejp_4710_;
}
v_reusejp_4710_:
{
return v___x_4711_;
}
}
}
}
else
{
return v___x_4700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4714_, lean_object* v___x_4715_, lean_object* v___x_4716_, lean_object* v___x_4717_, lean_object* v_fvs_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
uint8_t v___x_12406__boxed_4726_; lean_object* v_res_4727_; 
v___x_12406__boxed_4726_ = lean_unbox(v___x_4716_);
v_res_4727_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(v_frameStx_4714_, v___x_4715_, v___x_12406__boxed_4726_, v___x_4717_, v_fvs_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec_ref(v_fvs_4718_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4733_, lean_object* v_frameStx_4734_, lean_object* v___f_4735_, lean_object* v_fvs_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v___x_4749_; uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___f_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; uint8_t v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; 
v___x_4749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4749_, 0, v_resourceTy_4733_);
v___x_4750_ = 1;
v___x_4751_ = lean_box(0);
v___x_4752_ = lean_box(v___x_4750_);
v___f_4753_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4753_, 0, v_frameStx_4734_);
lean_closure_set(v___f_4753_, 1, v___x_4749_);
lean_closure_set(v___f_4753_, 2, v___x_4752_);
lean_closure_set(v___f_4753_, 3, v___x_4751_);
lean_closure_set(v___f_4753_, 4, v_fvs_4736_);
v___x_4754_ = lean_box(0);
v___x_4755_ = lean_box(1);
v___x_4756_ = 0;
v___x_4757_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0));
v___x_4758_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4758_, 0, v___x_4751_);
lean_ctor_set(v___x_4758_, 1, v___x_4754_);
lean_ctor_set(v___x_4758_, 2, v___x_4751_);
lean_ctor_set(v___x_4758_, 3, v___f_4735_);
lean_ctor_set(v___x_4758_, 4, v___x_4755_);
lean_ctor_set(v___x_4758_, 5, v___x_4755_);
lean_ctor_set(v___x_4758_, 6, v___x_4751_);
lean_ctor_set(v___x_4758_, 7, v___x_4757_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8, v___x_4750_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 1, v___x_4750_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 2, v___x_4750_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 3, v___x_4750_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 4, v___x_4756_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 5, v___x_4756_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 6, v___x_4756_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 7, v___x_4756_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 8, v___x_4750_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 9, v___x_4756_);
lean_ctor_set_uint8(v___x_4758_, sizeof(void*)*8 + 10, v___x_4750_);
v___x_4759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1));
v___x_4760_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4753_, v___x_4758_, v___x_4759_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
if (lean_obj_tag(v___x_4760_) == 0)
{
lean_object* v_a_4761_; lean_object* v_fst_4762_; lean_object* v___x_4763_; 
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref_known(v___x_4760_, 1);
v_fst_4762_ = lean_ctor_get(v_a_4761_, 0);
lean_inc(v_fst_4762_);
lean_dec(v_a_4761_);
v___x_4763_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4762_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
return v___x_4763_;
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
v_a_4764_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4760_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4760_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_4772_, lean_object* v_frameStx_4773_, lean_object* v___f_4774_, lean_object* v_fvs_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(v_resourceTy_4772_, v_frameStx_4773_, v___f_4774_, v_fvs_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object* v_as_4789_, size_t v_sz_4790_, size_t v_i_4791_, lean_object* v_b_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v_a_4799_; uint8_t v___x_4803_; 
v___x_4803_ = lean_usize_dec_lt(v_i_4791_, v_sz_4790_);
if (v___x_4803_ == 0)
{
lean_object* v___x_4804_; 
v___x_4804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4804_, 0, v_b_4792_);
return v___x_4804_;
}
else
{
lean_object* v_snd_4805_; lean_object* v_fst_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4852_; 
v_snd_4805_ = lean_ctor_get(v_b_4792_, 1);
v_fst_4806_ = lean_ctor_get(v_b_4792_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v_b_4792_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4808_ = v_b_4792_;
v_isShared_4809_ = v_isSharedCheck_4852_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_snd_4805_);
lean_inc(v_fst_4806_);
lean_dec(v_b_4792_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4852_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v_array_4810_; lean_object* v_start_4811_; lean_object* v_stop_4812_; uint8_t v___x_4813_; 
v_array_4810_ = lean_ctor_get(v_snd_4805_, 0);
v_start_4811_ = lean_ctor_get(v_snd_4805_, 1);
v_stop_4812_ = lean_ctor_get(v_snd_4805_, 2);
v___x_4813_ = lean_nat_dec_lt(v_start_4811_, v_stop_4812_);
if (v___x_4813_ == 0)
{
lean_object* v___x_4815_; 
if (v_isShared_4809_ == 0)
{
v___x_4815_ = v___x_4808_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_fst_4806_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_snd_4805_);
v___x_4815_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
}
else
{
lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4848_; 
lean_inc(v_stop_4812_);
lean_inc(v_start_4811_);
lean_inc_ref(v_array_4810_);
v_isSharedCheck_4848_ = !lean_is_exclusive(v_snd_4805_);
if (v_isSharedCheck_4848_ == 0)
{
lean_object* v_unused_4849_; lean_object* v_unused_4850_; lean_object* v_unused_4851_; 
v_unused_4849_ = lean_ctor_get(v_snd_4805_, 2);
lean_dec(v_unused_4849_);
v_unused_4850_ = lean_ctor_get(v_snd_4805_, 1);
lean_dec(v_unused_4850_);
v_unused_4851_ = lean_ctor_get(v_snd_4805_, 0);
lean_dec(v_unused_4851_);
v___x_4819_ = v_snd_4805_;
v_isShared_4820_ = v_isSharedCheck_4848_;
goto v_resetjp_4818_;
}
else
{
lean_dec(v_snd_4805_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4848_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v_a_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; lean_object* v___x_4826_; 
v_a_4821_ = lean_array_uget_borrowed(v_as_4789_, v_i_4791_);
v___x_4822_ = lean_array_fget(v_array_4810_, v_start_4811_);
v___x_4823_ = lean_unsigned_to_nat(1u);
v___x_4824_ = lean_nat_add(v_start_4811_, v___x_4823_);
lean_dec(v_start_4811_);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 1, v___x_4824_);
v___x_4826_ = v___x_4819_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_array_4810_);
lean_ctor_set(v_reuseFailAlloc_4847_, 1, v___x_4824_);
lean_ctor_set(v_reuseFailAlloc_4847_, 2, v_stop_4812_);
v___x_4826_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
if (lean_obj_tag(v_a_4821_) == 1)
{
lean_object* v_val_4827_; lean_object* v___x_4828_; 
v_val_4827_ = lean_ctor_get(v_a_4821_, 0);
lean_inc(v___y_4796_);
lean_inc_ref(v___y_4795_);
lean_inc(v___y_4794_);
lean_inc_ref(v___y_4793_);
lean_inc(v___x_4822_);
v___x_4828_ = lean_infer_type(v___x_4822_, v___y_4793_, v___y_4794_, v___y_4795_, v___y_4796_);
if (lean_obj_tag(v___x_4828_) == 0)
{
lean_object* v_a_4829_; lean_object* v___x_4831_; 
v_a_4829_ = lean_ctor_get(v___x_4828_, 0);
lean_inc(v_a_4829_);
lean_dec_ref_known(v___x_4828_, 1);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 1, v___x_4822_);
lean_ctor_set(v___x_4808_, 0, v_a_4829_);
v___x_4831_ = v___x_4808_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v___x_4822_);
v___x_4831_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
lean_inc(v_val_4827_);
v___x_4832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4832_, 0, v_val_4827_);
lean_ctor_set(v___x_4832_, 1, v___x_4831_);
v___x_4833_ = lean_array_push(v_fst_4806_, v___x_4832_);
v___x_4834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4833_);
lean_ctor_set(v___x_4834_, 1, v___x_4826_);
v_a_4799_ = v___x_4834_;
goto v___jp_4798_;
}
}
else
{
lean_object* v_a_4836_; lean_object* v___x_4838_; uint8_t v_isShared_4839_; uint8_t v_isSharedCheck_4843_; 
lean_dec_ref(v___x_4826_);
lean_dec(v___x_4822_);
lean_del_object(v___x_4808_);
lean_dec(v_fst_4806_);
v_a_4836_ = lean_ctor_get(v___x_4828_, 0);
v_isSharedCheck_4843_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4843_ == 0)
{
v___x_4838_ = v___x_4828_;
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
else
{
lean_inc(v_a_4836_);
lean_dec(v___x_4828_);
v___x_4838_ = lean_box(0);
v_isShared_4839_ = v_isSharedCheck_4843_;
goto v_resetjp_4837_;
}
v_resetjp_4837_:
{
lean_object* v___x_4841_; 
if (v_isShared_4839_ == 0)
{
v___x_4841_ = v___x_4838_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v_a_4836_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
}
else
{
lean_object* v___x_4845_; 
lean_dec(v___x_4822_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 1, v___x_4826_);
v___x_4845_ = v___x_4808_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4846_; 
v_reuseFailAlloc_4846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4846_, 0, v_fst_4806_);
lean_ctor_set(v_reuseFailAlloc_4846_, 1, v___x_4826_);
v___x_4845_ = v_reuseFailAlloc_4846_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
v_a_4799_ = v___x_4845_;
goto v___jp_4798_;
}
}
}
}
}
}
}
v___jp_4798_:
{
size_t v___x_4800_; size_t v___x_4801_; 
v___x_4800_ = ((size_t)1ULL);
v___x_4801_ = lean_usize_add(v_i_4791_, v___x_4800_);
v_i_4791_ = v___x_4801_;
v_b_4792_ = v_a_4799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_as_4853_, lean_object* v_sz_4854_, lean_object* v_i_4855_, lean_object* v_b_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
size_t v_sz_boxed_4862_; size_t v_i_boxed_4863_; lean_object* v_res_4864_; 
v_sz_boxed_4862_ = lean_unbox_usize(v_sz_4854_);
lean_dec(v_sz_4854_);
v_i_boxed_4863_ = lean_unbox_usize(v_i_4855_);
lean_dec(v_i_4855_);
v_res_4864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_as_4853_, v_sz_boxed_4862_, v_i_boxed_4863_, v_b_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec_ref(v_as_4853_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object* v_resourceTy_4868_, lean_object* v_entry_4869_, lean_object* v_res_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_, lean_object* v_a_4875_, lean_object* v_a_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v_a_4879_, lean_object* v_a_4880_, lean_object* v_a_4881_){
_start:
{
lean_object* v_args_4883_; lean_object* v_varNames_4884_; lean_object* v_frameStx_4885_; lean_object* v___x_4886_; lean_object* v_decls_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; size_t v_sz_4891_; size_t v___x_4892_; lean_object* v___x_4893_; 
v_args_4883_ = lean_ctor_get(v_res_4870_, 1);
lean_inc_ref(v_args_4883_);
lean_dec_ref(v_res_4870_);
v_varNames_4884_ = lean_ctor_get(v_entry_4869_, 1);
lean_inc_ref(v_varNames_4884_);
v_frameStx_4885_ = lean_ctor_get(v_entry_4869_, 2);
lean_inc(v_frameStx_4885_);
lean_dec_ref(v_entry_4869_);
v___x_4886_ = lean_unsigned_to_nat(0u);
v_decls_4887_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0));
v___x_4888_ = lean_array_get_size(v_args_4883_);
v___x_4889_ = l_Array_toSubarray___redArg(v_args_4883_, v___x_4886_, v___x_4888_);
v___x_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4890_, 0, v_decls_4887_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
v_sz_4891_ = lean_array_size(v_varNames_4884_);
v___x_4892_ = ((size_t)0ULL);
v___x_4893_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_varNames_4884_, v_sz_4891_, v___x_4892_, v___x_4890_, v_a_4878_, v_a_4879_, v_a_4880_, v_a_4881_);
lean_dec_ref(v_varNames_4884_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; lean_object* v_fst_4895_; lean_object* v_keyedConfig_4896_; uint8_t v_trackZetaDelta_4897_; lean_object* v_zetaDeltaSet_4898_; lean_object* v_lctx_4899_; lean_object* v_localInstances_4900_; lean_object* v_defEqCtx_x3f_4901_; lean_object* v_synthPendingDepth_4902_; lean_object* v_customCanUnfoldPredicate_x3f_4903_; uint8_t v_univApprox_4904_; uint8_t v_inTypeClassResolution_4905_; uint8_t v_cacheInferType_4906_; lean_object* v___f_4907_; lean_object* v___f_4908_; uint8_t v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref_known(v___x_4893_, 1);
v_fst_4895_ = lean_ctor_get(v_a_4894_, 0);
lean_inc(v_fst_4895_);
lean_dec(v_a_4894_);
v_keyedConfig_4896_ = lean_ctor_get(v_a_4878_, 0);
v_trackZetaDelta_4897_ = lean_ctor_get_uint8(v_a_4878_, sizeof(void*)*7);
v_zetaDeltaSet_4898_ = lean_ctor_get(v_a_4878_, 1);
v_lctx_4899_ = lean_ctor_get(v_a_4878_, 2);
v_localInstances_4900_ = lean_ctor_get(v_a_4878_, 3);
v_defEqCtx_x3f_4901_ = lean_ctor_get(v_a_4878_, 4);
v_synthPendingDepth_4902_ = lean_ctor_get(v_a_4878_, 5);
v_customCanUnfoldPredicate_x3f_4903_ = lean_ctor_get(v_a_4878_, 6);
v_univApprox_4904_ = lean_ctor_get_uint8(v_a_4878_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4905_ = lean_ctor_get_uint8(v_a_4878_, sizeof(void*)*7 + 2);
v_cacheInferType_4906_ = lean_ctor_get_uint8(v_a_4878_, sizeof(void*)*7 + 3);
v___f_4907_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1));
v___f_4908_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4908_, 0, v_resourceTy_4868_);
lean_closure_set(v___f_4908_, 1, v_frameStx_4885_);
lean_closure_set(v___f_4908_, 2, v___f_4907_);
v___x_4909_ = 1;
lean_inc_ref(v_keyedConfig_4896_);
v___x_4910_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4909_, v_keyedConfig_4896_);
lean_inc(v_customCanUnfoldPredicate_x3f_4903_);
lean_inc(v_synthPendingDepth_4902_);
lean_inc(v_defEqCtx_x3f_4901_);
lean_inc_ref(v_localInstances_4900_);
lean_inc_ref(v_lctx_4899_);
lean_inc(v_zetaDeltaSet_4898_);
v___x_4911_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
lean_ctor_set(v___x_4911_, 1, v_zetaDeltaSet_4898_);
lean_ctor_set(v___x_4911_, 2, v_lctx_4899_);
lean_ctor_set(v___x_4911_, 3, v_localInstances_4900_);
lean_ctor_set(v___x_4911_, 4, v_defEqCtx_x3f_4901_);
lean_ctor_set(v___x_4911_, 5, v_synthPendingDepth_4902_);
lean_ctor_set(v___x_4911_, 6, v_customCanUnfoldPredicate_x3f_4903_);
lean_ctor_set_uint8(v___x_4911_, sizeof(void*)*7, v_trackZetaDelta_4897_);
lean_ctor_set_uint8(v___x_4911_, sizeof(void*)*7 + 1, v_univApprox_4904_);
lean_ctor_set_uint8(v___x_4911_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4905_);
lean_ctor_set_uint8(v___x_4911_, sizeof(void*)*7 + 3, v_cacheInferType_4906_);
v___x_4912_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_fst_4895_, v___f_4908_, v_decls_4887_, v_a_4871_, v_a_4872_, v_a_4873_, v_a_4874_, v_a_4875_, v_a_4876_, v_a_4877_, v___x_4911_, v_a_4879_, v_a_4880_, v_a_4881_);
lean_dec_ref_known(v___x_4911_, 7);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4920_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4920_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4920_ == 0)
{
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4920_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___x_4918_; 
if (v_isShared_4916_ == 0)
{
v___x_4918_ = v___x_4915_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v_a_4913_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
return v___x_4918_;
}
}
}
else
{
return v___x_4912_;
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v_frameStx_4885_);
lean_dec_ref(v_resourceTy_4868_);
v_a_4921_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4893_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4893_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object* v_resourceTy_4929_, lean_object* v_entry_4930_, lean_object* v_res_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_){
_start:
{
lean_object* v_res_4944_; 
v_res_4944_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_resourceTy_4929_, v_entry_4930_, v_res_4931_, v_a_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_);
lean_dec(v_a_4942_);
lean_dec_ref(v_a_4941_);
lean_dec(v_a_4940_);
lean_dec_ref(v_a_4939_);
lean_dec(v_a_4938_);
lean_dec_ref(v_a_4937_);
lean_dec(v_a_4936_);
lean_dec_ref(v_a_4935_);
lean_dec(v_a_4934_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
return v_res_4944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object* v_as_4945_, size_t v_sz_4946_, size_t v_i_4947_, lean_object* v_b_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_){
_start:
{
lean_object* v___x_4961_; 
v___x_4961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_as_4945_, v_sz_4946_, v_i_4947_, v_b_4948_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
return v___x_4961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object* v_as_4962_, lean_object* v_sz_4963_, lean_object* v_i_4964_, lean_object* v_b_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
size_t v_sz_boxed_4978_; size_t v_i_boxed_4979_; lean_object* v_res_4980_; 
v_sz_boxed_4978_ = lean_unbox_usize(v_sz_4963_);
lean_dec(v_sz_4963_);
v_i_boxed_4979_ = lean_unbox_usize(v_i_4964_);
lean_dec(v_i_4964_);
v_res_4980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(v_as_4962_, v_sz_boxed_4978_, v_i_boxed_4979_, v_b_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
lean_dec(v___y_4976_);
lean_dec_ref(v___y_4975_);
lean_dec(v___y_4974_);
lean_dec_ref(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
lean_dec(v___y_4970_);
lean_dec_ref(v___y_4969_);
lean_dec(v___y_4968_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec_ref(v_as_4962_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_4981_, lean_object* v___x_4982_, lean_object* v_as_4983_, size_t v_sz_4984_, size_t v_i_4985_, lean_object* v_b_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v_a_4995_; uint8_t v___x_4999_; 
v___x_4999_ = lean_usize_dec_lt(v_i_4985_, v_sz_4984_);
if (v___x_4999_ == 0)
{
lean_object* v___x_5000_; 
lean_dec_ref(v___x_4982_);
v___x_5000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5000_, 0, v_b_4986_);
return v___x_5000_;
}
else
{
lean_object* v_a_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; uint8_t v_retired_5004_; 
v_a_5001_ = lean_array_uget_borrowed(v_as_4983_, v_i_4985_);
v___x_5002_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
v___x_5003_ = lean_array_get_borrowed(v___x_5002_, v___x_4981_, v_a_5001_);
v_retired_5004_ = lean_ctor_get_uint8(v___x_5003_, sizeof(void*)*4);
if (v_retired_5004_ == 0)
{
lean_object* v_pat_5005_; lean_object* v_srcIdx_5006_; lean_object* v___x_5007_; 
v_pat_5005_ = lean_ctor_get(v___x_5003_, 0);
v_srcIdx_5006_ = lean_ctor_get(v___x_5003_, 3);
lean_inc_ref(v___x_4982_);
lean_inc_ref(v_pat_5005_);
v___x_5007_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_5005_, v___x_4982_, v___x_4999_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v_a_5008_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
lean_inc(v_a_5008_);
lean_dec_ref_known(v___x_5007_, 1);
if (lean_obj_tag(v_a_5008_) == 1)
{
if (lean_obj_tag(v_b_4986_) == 0)
{
lean_object* v_val_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5017_; 
v_val_5009_ = lean_ctor_get(v_a_5008_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_a_5008_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5011_ = v_a_5008_;
v_isShared_5012_ = v_isSharedCheck_5017_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_val_5009_);
lean_dec(v_a_5008_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5017_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
lean_inc(v___x_5003_);
v___x_5013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5013_, 0, v___x_5003_);
lean_ctor_set(v___x_5013_, 1, v_val_5009_);
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5013_);
v___x_5015_ = v___x_5011_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5013_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
v_a_4995_ = v___x_5015_;
goto v___jp_4994_;
}
}
}
else
{
lean_object* v_val_5018_; lean_object* v_fst_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5037_; 
v_val_5018_ = lean_ctor_get(v_b_4986_, 0);
lean_inc(v_val_5018_);
v_fst_5019_ = lean_ctor_get(v_val_5018_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v_val_5018_);
if (v_isSharedCheck_5037_ == 0)
{
lean_object* v_unused_5038_; 
v_unused_5038_ = lean_ctor_get(v_val_5018_, 1);
lean_dec(v_unused_5038_);
v___x_5021_ = v_val_5018_;
v_isShared_5022_ = v_isSharedCheck_5037_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_fst_5019_);
lean_dec(v_val_5018_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5037_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v_val_5023_; lean_object* v_srcIdx_5024_; uint8_t v___x_5025_; 
v_val_5023_ = lean_ctor_get(v_a_5008_, 0);
lean_inc(v_val_5023_);
lean_dec_ref_known(v_a_5008_, 1);
v_srcIdx_5024_ = lean_ctor_get(v_fst_5019_, 3);
lean_inc(v_srcIdx_5024_);
lean_dec(v_fst_5019_);
v___x_5025_ = lean_nat_dec_lt(v_srcIdx_5006_, v_srcIdx_5024_);
lean_dec(v_srcIdx_5024_);
if (v___x_5025_ == 0)
{
lean_dec(v_val_5023_);
lean_del_object(v___x_5021_);
v_a_4995_ = v_b_4986_;
goto v___jp_4994_;
}
else
{
lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5035_; 
v_isSharedCheck_5035_ = !lean_is_exclusive(v_b_4986_);
if (v_isSharedCheck_5035_ == 0)
{
lean_object* v_unused_5036_; 
v_unused_5036_ = lean_ctor_get(v_b_4986_, 0);
lean_dec(v_unused_5036_);
v___x_5027_ = v_b_4986_;
v_isShared_5028_ = v_isSharedCheck_5035_;
goto v_resetjp_5026_;
}
else
{
lean_dec(v_b_4986_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5035_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v___x_5030_; 
lean_inc(v___x_5003_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 1, v_val_5023_);
lean_ctor_set(v___x_5021_, 0, v___x_5003_);
v___x_5030_ = v___x_5021_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5034_; 
v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5003_);
lean_ctor_set(v_reuseFailAlloc_5034_, 1, v_val_5023_);
v___x_5030_ = v_reuseFailAlloc_5034_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
lean_object* v___x_5032_; 
if (v_isShared_5028_ == 0)
{
lean_ctor_set(v___x_5027_, 0, v___x_5030_);
v___x_5032_ = v___x_5027_;
goto v_reusejp_5031_;
}
else
{
lean_object* v_reuseFailAlloc_5033_; 
v_reuseFailAlloc_5033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5030_);
v___x_5032_ = v_reuseFailAlloc_5033_;
goto v_reusejp_5031_;
}
v_reusejp_5031_:
{
v_a_4995_ = v___x_5032_;
goto v___jp_4994_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_5008_);
v_a_4995_ = v_b_4986_;
goto v___jp_4994_;
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5046_; 
lean_dec(v_b_4986_);
lean_dec_ref(v___x_4982_);
v_a_5039_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5046_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5046_ == 0)
{
v___x_5041_ = v___x_5007_;
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v___x_5007_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5046_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5044_; 
if (v_isShared_5042_ == 0)
{
v___x_5044_ = v___x_5041_;
goto v_reusejp_5043_;
}
else
{
lean_object* v_reuseFailAlloc_5045_; 
v_reuseFailAlloc_5045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5045_, 0, v_a_5039_);
v___x_5044_ = v_reuseFailAlloc_5045_;
goto v_reusejp_5043_;
}
v_reusejp_5043_:
{
return v___x_5044_;
}
}
}
}
else
{
v_a_4995_ = v_b_4986_;
goto v___jp_4994_;
}
}
v___jp_4994_:
{
size_t v___x_4996_; size_t v___x_4997_; 
v___x_4996_ = ((size_t)1ULL);
v___x_4997_ = lean_usize_add(v_i_4985_, v___x_4996_);
v_i_4985_ = v___x_4997_;
v_b_4986_ = v_a_4995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_5047_, lean_object* v___x_5048_, lean_object* v_as_5049_, lean_object* v_sz_5050_, lean_object* v_i_5051_, lean_object* v_b_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_, lean_object* v___y_5057_, lean_object* v___y_5058_, lean_object* v___y_5059_){
_start:
{
size_t v_sz_boxed_5060_; size_t v_i_boxed_5061_; lean_object* v_res_5062_; 
v_sz_boxed_5060_ = lean_unbox_usize(v_sz_5050_);
lean_dec(v_sz_5050_);
v_i_boxed_5061_ = lean_unbox_usize(v_i_5051_);
lean_dec(v_i_5051_);
v_res_5062_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5047_, v___x_5048_, v_as_5049_, v_sz_boxed_5060_, v_i_boxed_5061_, v_b_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_);
lean_dec(v___y_5058_);
lean_dec_ref(v___y_5057_);
lean_dec(v___y_5056_);
lean_dec_ref(v___y_5055_);
lean_dec(v___y_5054_);
lean_dec_ref(v___y_5053_);
lean_dec_ref(v_as_5049_);
lean_dec_ref(v___x_5047_);
return v_res_5062_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0));
v___x_5065_ = l_Lean_stringToMessageData(v___x_5064_);
return v___x_5065_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2));
v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object* v_fp_5069_, lean_object* v_info_5070_, lean_object* v_a_5071_, lean_object* v_a_5072_, lean_object* v_a_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_, lean_object* v_a_5077_, lean_object* v_a_5078_, lean_object* v_a_5079_, lean_object* v_a_5080_, lean_object* v_a_5081_){
_start:
{
lean_object* v___x_5083_; lean_object* v_frameDB_5084_; lean_object* v_tree_5085_; lean_object* v_entries_5086_; lean_object* v___x_5088_; uint8_t v_isShared_5089_; uint8_t v_isSharedCheck_5221_; 
v___x_5083_ = lean_st_ref_get(v_a_5072_);
v_frameDB_5084_ = lean_ctor_get(v___x_5083_, 4);
lean_inc_ref(v_frameDB_5084_);
lean_dec(v___x_5083_);
v_tree_5085_ = lean_ctor_get(v_frameDB_5084_, 0);
v_entries_5086_ = lean_ctor_get(v_frameDB_5084_, 1);
v_isSharedCheck_5221_ = !lean_is_exclusive(v_frameDB_5084_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5088_ = v_frameDB_5084_;
v_isShared_5089_ = v_isSharedCheck_5221_;
goto v_resetjp_5087_;
}
else
{
lean_inc(v_entries_5086_);
lean_inc(v_tree_5085_);
lean_dec(v_frameDB_5084_);
v___x_5088_ = lean_box(0);
v_isShared_5089_ = v_isSharedCheck_5221_;
goto v_resetjp_5087_;
}
v_resetjp_5087_:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; uint8_t v___x_5092_; 
v___x_5090_ = lean_array_get_size(v_entries_5086_);
v___x_5091_ = lean_unsigned_to_nat(0u);
v___x_5092_ = lean_nat_dec_eq(v___x_5090_, v___x_5091_);
if (v___x_5092_ == 0)
{
lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; size_t v_sz_5096_; size_t v___x_5097_; lean_object* v___x_5098_; 
v___x_5093_ = lean_box(0);
v___x_5094_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_5070_);
v___x_5095_ = l_Lean_Meta_Sym_getMatch___redArg(v_tree_5085_, v___x_5094_);
lean_dec_ref(v_tree_5085_);
v_sz_5096_ = lean_array_size(v___x_5095_);
v___x_5097_ = ((size_t)0ULL);
lean_inc_ref(v___x_5094_);
v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_entries_5086_, v___x_5094_, v___x_5095_, v_sz_5096_, v___x_5097_, v___x_5093_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
lean_dec_ref(v___x_5095_);
lean_dec_ref(v_entries_5086_);
if (lean_obj_tag(v___x_5098_) == 0)
{
lean_object* v_a_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5210_; 
v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5210_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5210_ == 0)
{
v___x_5101_ = v___x_5098_;
v_isShared_5102_ = v_isSharedCheck_5210_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_a_5099_);
lean_dec(v___x_5098_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5210_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
if (lean_obj_tag(v_a_5099_) == 1)
{
lean_object* v_val_5103_; lean_object* v___x_5105_; uint8_t v_isShared_5106_; uint8_t v_isSharedCheck_5206_; 
lean_del_object(v___x_5101_);
v_val_5103_ = lean_ctor_get(v_a_5099_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v_a_5099_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5105_ = v_a_5099_;
v_isShared_5106_ = v_isSharedCheck_5206_;
goto v_resetjp_5104_;
}
else
{
lean_inc(v_val_5103_);
lean_dec(v_a_5099_);
v___x_5105_ = lean_box(0);
v_isShared_5106_ = v_isSharedCheck_5206_;
goto v_resetjp_5104_;
}
v_resetjp_5104_:
{
lean_object* v_fst_5107_; lean_object* v_snd_5108_; lean_object* v___x_5110_; uint8_t v_isShared_5111_; uint8_t v_isSharedCheck_5205_; 
v_fst_5107_ = lean_ctor_get(v_val_5103_, 0);
v_snd_5108_ = lean_ctor_get(v_val_5103_, 1);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_val_5103_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5110_ = v_val_5103_;
v_isShared_5111_ = v_isSharedCheck_5205_;
goto v_resetjp_5109_;
}
else
{
lean_inc(v_snd_5108_);
lean_inc(v_fst_5107_);
lean_dec(v_val_5103_);
v___x_5110_ = lean_box(0);
v_isShared_5111_ = v_isSharedCheck_5205_;
goto v_resetjp_5109_;
}
v_resetjp_5109_:
{
lean_object* v___x_5112_; lean_object* v_frameDB_5113_; lean_object* v_specBackwardRuleCache_5114_; lean_object* v_splitBackwardRuleCache_5115_; lean_object* v_latticeBackwardRuleCache_5116_; lean_object* v_frameBackwardRuleCache_5117_; lean_object* v_invariants_5118_; lean_object* v_vcs_5119_; lean_object* v_simpState_5120_; lean_object* v_fuel_5121_; lean_object* v_inlineHandledInvariants_5122_; lean_object* v___x_5124_; uint8_t v_isShared_5125_; uint8_t v_isSharedCheck_5204_; 
v___x_5112_ = lean_st_ref_take(v_a_5072_);
v_frameDB_5113_ = lean_ctor_get(v___x_5112_, 4);
v_specBackwardRuleCache_5114_ = lean_ctor_get(v___x_5112_, 0);
v_splitBackwardRuleCache_5115_ = lean_ctor_get(v___x_5112_, 1);
v_latticeBackwardRuleCache_5116_ = lean_ctor_get(v___x_5112_, 2);
v_frameBackwardRuleCache_5117_ = lean_ctor_get(v___x_5112_, 3);
v_invariants_5118_ = lean_ctor_get(v___x_5112_, 5);
v_vcs_5119_ = lean_ctor_get(v___x_5112_, 6);
v_simpState_5120_ = lean_ctor_get(v___x_5112_, 7);
v_fuel_5121_ = lean_ctor_get(v___x_5112_, 8);
v_inlineHandledInvariants_5122_ = lean_ctor_get(v___x_5112_, 9);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5112_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5124_ = v___x_5112_;
v_isShared_5125_ = v_isSharedCheck_5204_;
goto v_resetjp_5123_;
}
else
{
lean_inc(v_inlineHandledInvariants_5122_);
lean_inc(v_fuel_5121_);
lean_inc(v_simpState_5120_);
lean_inc(v_vcs_5119_);
lean_inc(v_invariants_5118_);
lean_inc(v_frameDB_5113_);
lean_inc(v_frameBackwardRuleCache_5117_);
lean_inc(v_latticeBackwardRuleCache_5116_);
lean_inc(v_splitBackwardRuleCache_5115_);
lean_inc(v_specBackwardRuleCache_5114_);
lean_dec(v___x_5112_);
v___x_5124_ = lean_box(0);
v_isShared_5125_ = v_isSharedCheck_5204_;
goto v_resetjp_5123_;
}
v_resetjp_5123_:
{
lean_object* v_tree_5126_; lean_object* v_entries_5127_; lean_object* v___x_5129_; uint8_t v_isShared_5130_; uint8_t v_isSharedCheck_5203_; 
v_tree_5126_ = lean_ctor_get(v_frameDB_5113_, 0);
v_entries_5127_ = lean_ctor_get(v_frameDB_5113_, 1);
v_isSharedCheck_5203_ = !lean_is_exclusive(v_frameDB_5113_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5129_ = v_frameDB_5113_;
v_isShared_5130_ = v_isSharedCheck_5203_;
goto v_resetjp_5128_;
}
else
{
lean_inc(v_entries_5127_);
lean_inc(v_tree_5126_);
lean_dec(v_frameDB_5113_);
v___x_5129_ = lean_box(0);
v_isShared_5130_ = v_isSharedCheck_5203_;
goto v_resetjp_5128_;
}
v_resetjp_5128_:
{
lean_object* v_pat_5131_; lean_object* v_varNames_5132_; lean_object* v_frameStx_5133_; lean_object* v_srcIdx_5134_; uint8_t v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5139_; 
v_pat_5131_ = lean_ctor_get(v_fst_5107_, 0);
v_varNames_5132_ = lean_ctor_get(v_fst_5107_, 1);
v_frameStx_5133_ = lean_ctor_get(v_fst_5107_, 2);
v_srcIdx_5134_ = lean_ctor_get(v_fst_5107_, 3);
v___x_5135_ = 1;
lean_inc(v_srcIdx_5134_);
lean_inc(v_frameStx_5133_);
lean_inc_ref(v_varNames_5132_);
lean_inc_ref(v_pat_5131_);
v___x_5136_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5136_, 0, v_pat_5131_);
lean_ctor_set(v___x_5136_, 1, v_varNames_5132_);
lean_ctor_set(v___x_5136_, 2, v_frameStx_5133_);
lean_ctor_set(v___x_5136_, 3, v_srcIdx_5134_);
lean_ctor_set_uint8(v___x_5136_, sizeof(void*)*4, v___x_5135_);
v___x_5137_ = lean_array_set(v_entries_5127_, v_srcIdx_5134_, v___x_5136_);
if (v_isShared_5130_ == 0)
{
lean_ctor_set(v___x_5129_, 1, v___x_5137_);
v___x_5139_ = v___x_5129_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_tree_5126_);
lean_ctor_set(v_reuseFailAlloc_5202_, 1, v___x_5137_);
v___x_5139_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5141_; 
if (v_isShared_5125_ == 0)
{
lean_ctor_set(v___x_5124_, 4, v___x_5139_);
v___x_5141_ = v___x_5124_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_specBackwardRuleCache_5114_);
lean_ctor_set(v_reuseFailAlloc_5201_, 1, v_splitBackwardRuleCache_5115_);
lean_ctor_set(v_reuseFailAlloc_5201_, 2, v_latticeBackwardRuleCache_5116_);
lean_ctor_set(v_reuseFailAlloc_5201_, 3, v_frameBackwardRuleCache_5117_);
lean_ctor_set(v_reuseFailAlloc_5201_, 4, v___x_5139_);
lean_ctor_set(v_reuseFailAlloc_5201_, 5, v_invariants_5118_);
lean_ctor_set(v_reuseFailAlloc_5201_, 6, v_vcs_5119_);
lean_ctor_set(v_reuseFailAlloc_5201_, 7, v_simpState_5120_);
lean_ctor_set(v_reuseFailAlloc_5201_, 8, v_fuel_5121_);
lean_ctor_set(v_reuseFailAlloc_5201_, 9, v_inlineHandledInvariants_5122_);
v___x_5141_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
lean_object* v___x_5142_; lean_object* v_mkResourceTy_5143_; lean_object* v___x_5144_; 
v___x_5142_ = lean_st_ref_set(v_a_5072_, v___x_5141_);
v_mkResourceTy_5143_ = lean_ctor_get(v_fp_5069_, 3);
lean_inc_ref(v_mkResourceTy_5143_);
lean_dec_ref(v_fp_5069_);
lean_inc(v_a_5081_);
lean_inc_ref(v_a_5080_);
lean_inc(v_a_5079_);
lean_inc_ref(v_a_5078_);
v___x_5144_ = lean_apply_6(v_mkResourceTy_5143_, v_info_5070_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_, lean_box(0));
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5146_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_a_5145_, v_fst_5107_, v_snd_5108_, v_a_5071_, v_a_5072_, v_a_5073_, v_a_5074_, v_a_5075_, v_a_5076_, v_a_5077_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; lean_object* v___x_5149_; uint8_t v_isShared_5150_; uint8_t v_isSharedCheck_5184_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5184_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5184_ == 0)
{
v___x_5149_ = v___x_5146_;
v_isShared_5150_ = v_isSharedCheck_5184_;
goto v_resetjp_5148_;
}
else
{
lean_inc(v_a_5147_);
lean_dec(v___x_5146_);
v___x_5149_ = lean_box(0);
v_isShared_5150_ = v_isSharedCheck_5184_;
goto v_resetjp_5148_;
}
v_resetjp_5148_:
{
lean_object* v_options_5158_; uint8_t v_hasTrace_5159_; 
v_options_5158_ = lean_ctor_get(v_a_5080_, 2);
v_hasTrace_5159_ = lean_ctor_get_uint8(v_options_5158_, sizeof(void*)*1);
if (v_hasTrace_5159_ == 0)
{
lean_del_object(v___x_5110_);
lean_dec_ref(v___x_5094_);
lean_del_object(v___x_5088_);
goto v___jp_5151_;
}
else
{
lean_object* v_inheritedTraceOptions_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; uint8_t v___x_5163_; 
v_inheritedTraceOptions_5160_ = lean_ctor_get(v_a_5080_, 13);
v___x_5161_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_5162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5163_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5160_, v_options_5158_, v___x_5162_);
if (v___x_5163_ == 0)
{
lean_del_object(v___x_5110_);
lean_dec_ref(v___x_5094_);
lean_del_object(v___x_5088_);
goto v___jp_5151_;
}
else
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5167_; 
v___x_5164_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1);
v___x_5165_ = l_Lean_MessageData_ofExpr(v___x_5094_);
if (v_isShared_5111_ == 0)
{
lean_ctor_set_tag(v___x_5110_, 7);
lean_ctor_set(v___x_5110_, 1, v___x_5165_);
lean_ctor_set(v___x_5110_, 0, v___x_5164_);
v___x_5167_ = v___x_5110_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5164_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v___x_5165_);
v___x_5167_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5168_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_5089_ == 0)
{
lean_ctor_set_tag(v___x_5088_, 7);
lean_ctor_set(v___x_5088_, 1, v___x_5168_);
lean_ctor_set(v___x_5088_, 0, v___x_5167_);
v___x_5170_ = v___x_5088_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5167_);
lean_ctor_set(v_reuseFailAlloc_5182_, 1, v___x_5168_);
v___x_5170_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v___x_5173_; 
lean_inc(v_a_5147_);
v___x_5171_ = l_Lean_indentExpr(v_a_5147_);
v___x_5172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5172_, 0, v___x_5170_);
lean_ctor_set(v___x_5172_, 1, v___x_5171_);
v___x_5173_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5161_, v___x_5172_, v_a_5078_, v_a_5079_, v_a_5080_, v_a_5081_);
if (lean_obj_tag(v___x_5173_) == 0)
{
lean_dec_ref_known(v___x_5173_, 1);
goto v___jp_5151_;
}
else
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
lean_del_object(v___x_5149_);
lean_dec(v_a_5147_);
lean_del_object(v___x_5105_);
v_a_5174_ = lean_ctor_get(v___x_5173_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5173_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5176_ = v___x_5173_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5173_);
v___x_5176_ = lean_box(0);
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
v_resetjp_5175_:
{
lean_object* v___x_5179_; 
if (v_isShared_5177_ == 0)
{
v___x_5179_ = v___x_5176_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_a_5174_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
}
}
}
}
}
v___jp_5151_:
{
lean_object* v___x_5153_; 
if (v_isShared_5106_ == 0)
{
lean_ctor_set(v___x_5105_, 0, v_a_5147_);
v___x_5153_ = v___x_5105_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5157_; 
v_reuseFailAlloc_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5147_);
v___x_5153_ = v_reuseFailAlloc_5157_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
lean_object* v___x_5155_; 
if (v_isShared_5150_ == 0)
{
lean_ctor_set(v___x_5149_, 0, v___x_5153_);
v___x_5155_ = v___x_5149_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5153_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
}
}
else
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5192_; 
lean_del_object(v___x_5110_);
lean_del_object(v___x_5105_);
lean_dec_ref(v___x_5094_);
lean_del_object(v___x_5088_);
v_a_5185_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5192_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5192_ == 0)
{
v___x_5187_ = v___x_5146_;
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v___x_5146_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5192_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5190_; 
if (v_isShared_5188_ == 0)
{
v___x_5190_ = v___x_5187_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5185_);
v___x_5190_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
return v___x_5190_;
}
}
}
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_del_object(v___x_5110_);
lean_dec(v_snd_5108_);
lean_dec(v_fst_5107_);
lean_del_object(v___x_5105_);
lean_dec_ref(v___x_5094_);
lean_del_object(v___x_5088_);
v_a_5193_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5144_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5144_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
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
lean_object* v___x_5208_; 
lean_dec(v_a_5099_);
lean_dec_ref(v___x_5094_);
lean_del_object(v___x_5088_);
lean_dec_ref(v_info_5070_);
lean_dec_ref(v_fp_5069_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set(v___x_5101_, 0, v___x_5093_);
v___x_5208_ = v___x_5101_;
goto v_reusejp_5207_;
}
else
{
lean_object* v_reuseFailAlloc_5209_; 
v_reuseFailAlloc_5209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5209_, 0, v___x_5093_);
v___x_5208_ = v_reuseFailAlloc_5209_;
goto v_reusejp_5207_;
}
v_reusejp_5207_:
{
return v___x_5208_;
}
}
}
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
lean_dec_ref(v___x_5094_);
lean_del_object(v___x_5088_);
lean_dec_ref(v_info_5070_);
lean_dec_ref(v_fp_5069_);
v_a_5211_ = lean_ctor_get(v___x_5098_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5098_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5098_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
else
{
lean_object* v___x_5219_; lean_object* v___x_5220_; 
lean_del_object(v___x_5088_);
lean_dec_ref(v_entries_5086_);
lean_dec_ref(v_tree_5085_);
lean_dec_ref(v_info_5070_);
lean_dec_ref(v_fp_5069_);
v___x_5219_ = lean_box(0);
v___x_5220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5219_);
return v___x_5220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object* v_fp_5222_, lean_object* v_info_5223_, lean_object* v_a_5224_, lean_object* v_a_5225_, lean_object* v_a_5226_, lean_object* v_a_5227_, lean_object* v_a_5228_, lean_object* v_a_5229_, lean_object* v_a_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_){
_start:
{
lean_object* v_res_5236_; 
v_res_5236_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_fp_5222_, v_info_5223_, v_a_5224_, v_a_5225_, v_a_5226_, v_a_5227_, v_a_5228_, v_a_5229_, v_a_5230_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
lean_dec(v_a_5234_);
lean_dec_ref(v_a_5233_);
lean_dec(v_a_5232_);
lean_dec_ref(v_a_5231_);
lean_dec(v_a_5230_);
lean_dec_ref(v_a_5229_);
lean_dec(v_a_5228_);
lean_dec_ref(v_a_5227_);
lean_dec(v_a_5226_);
lean_dec(v_a_5225_);
lean_dec_ref(v_a_5224_);
return v_res_5236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_5237_, lean_object* v___x_5238_, lean_object* v_as_5239_, size_t v_sz_5240_, size_t v_i_5241_, lean_object* v_b_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_){
_start:
{
lean_object* v___x_5255_; 
v___x_5255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v___x_5237_, v___x_5238_, v_as_5239_, v_sz_5240_, v_i_5241_, v_b_5242_, v___y_5248_, v___y_5249_, v___y_5250_, v___y_5251_, v___y_5252_, v___y_5253_);
return v___x_5255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_5256_ = _args[0];
lean_object* v___x_5257_ = _args[1];
lean_object* v_as_5258_ = _args[2];
lean_object* v_sz_5259_ = _args[3];
lean_object* v_i_5260_ = _args[4];
lean_object* v_b_5261_ = _args[5];
lean_object* v___y_5262_ = _args[6];
lean_object* v___y_5263_ = _args[7];
lean_object* v___y_5264_ = _args[8];
lean_object* v___y_5265_ = _args[9];
lean_object* v___y_5266_ = _args[10];
lean_object* v___y_5267_ = _args[11];
lean_object* v___y_5268_ = _args[12];
lean_object* v___y_5269_ = _args[13];
lean_object* v___y_5270_ = _args[14];
lean_object* v___y_5271_ = _args[15];
lean_object* v___y_5272_ = _args[16];
lean_object* v___y_5273_ = _args[17];
_start:
{
size_t v_sz_boxed_5274_; size_t v_i_boxed_5275_; lean_object* v_res_5276_; 
v_sz_boxed_5274_ = lean_unbox_usize(v_sz_5259_);
lean_dec(v_sz_5259_);
v_i_boxed_5275_ = lean_unbox_usize(v_i_5260_);
lean_dec(v_i_5260_);
v_res_5276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(v___x_5256_, v___x_5257_, v_as_5258_, v_sz_boxed_5274_, v_i_boxed_5275_, v_b_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_);
lean_dec(v___y_5272_);
lean_dec_ref(v___y_5271_);
lean_dec(v___y_5270_);
lean_dec_ref(v___y_5269_);
lean_dec(v___y_5268_);
lean_dec_ref(v___y_5267_);
lean_dec(v___y_5266_);
lean_dec_ref(v___y_5265_);
lean_dec(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec_ref(v_as_5258_);
lean_dec_ref(v___x_5256_);
return v_res_5276_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(lean_object* v_post_5284_){
_start:
{
lean_object* v___y_5286_; uint8_t v___x_5291_; 
v___x_5291_ = l_Lean_Expr_isLambda(v_post_5284_);
if (v___x_5291_ == 0)
{
v___y_5286_ = v_post_5284_;
goto v___jp_5285_;
}
else
{
lean_object* v___x_5292_; 
v___x_5292_ = l_Lean_Expr_bindingBody_x21(v_post_5284_);
lean_dec_ref(v_post_5284_);
v___y_5286_ = v___x_5292_;
goto v___jp_5285_;
}
v___jp_5285_:
{
lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; uint8_t v___x_5290_; 
v___x_5287_ = l_Lean_Expr_consumeMData(v___y_5286_);
lean_dec_ref(v___y_5286_);
v___x_5288_ = l_Lean_Expr_getAppFn(v___x_5287_);
lean_dec_ref(v___x_5287_);
v___x_5289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2));
v___x_5290_ = l_Lean_Expr_isConstOf(v___x_5288_, v___x_5289_);
lean_dec_ref(v___x_5288_);
return v___x_5290_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___boxed(lean_object* v_post_5293_){
_start:
{
uint8_t v_res_5294_; lean_object* v_r_5295_; 
v_res_5294_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(v_post_5293_);
v_r_5295_ = lean_box(v_res_5294_);
return v_r_5295_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1(void){
_start:
{
lean_object* v___x_5297_; lean_object* v___x_5298_; 
v___x_5297_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0));
v___x_5298_ = l_Lean_stringToMessageData(v___x_5297_);
return v___x_5298_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3(void){
_start:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2));
v___x_5301_ = l_Lean_stringToMessageData(v___x_5300_);
return v___x_5301_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__5(void){
_start:
{
lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__4));
v___x_5304_ = l_Lean_stringToMessageData(v___x_5303_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(lean_object* v_goal_5305_, lean_object* v_info_5306_, lean_object* v_fp_5307_, lean_object* v_split_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_, lean_object* v_a_5312_, lean_object* v_a_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v___x_5321_; 
lean_inc_ref(v_info_5306_);
v___x_5321_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_fp_5307_, v_info_5306_, v_a_5310_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v_rule_5323_; lean_object* v_splitVCIdx_5324_; lean_object* v_frameIdx_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
lean_inc(v_a_5322_);
lean_dec_ref_known(v___x_5321_, 1);
v_rule_5323_ = lean_ctor_get(v_a_5322_, 0);
lean_inc_ref(v_rule_5323_);
v_splitVCIdx_5324_ = lean_ctor_get(v_a_5322_, 1);
lean_inc(v_splitVCIdx_5324_);
v_frameIdx_5325_ = lean_ctor_get(v_a_5322_, 2);
lean_inc(v_frameIdx_5325_);
lean_dec(v_a_5322_);
v___x_5326_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1);
v___x_5327_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_5306_);
v___x_5328_ = l_Lean_indentExpr(v___x_5327_);
lean_inc_ref(v___x_5328_);
v___x_5329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5326_);
lean_ctor_set(v___x_5329_, 1, v___x_5328_);
v___x_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5329_);
v___x_5331_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_rule_5323_, v_goal_5305_, v___x_5330_, v_a_5309_, v_a_5310_, v_a_5311_, v_a_5312_, v_a_5313_, v_a_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v_a_5332_; 
v_a_5332_ = lean_ctor_get(v___x_5331_, 0);
lean_inc(v_a_5332_);
lean_dec_ref_known(v___x_5331_, 1);
if (lean_obj_tag(v_a_5332_) == 1)
{
lean_object* v_mvarIds_5333_; lean_object* v_frame_5334_; lean_object* v_residualPre_5335_; lean_object* v_splitVCProof_5336_; lean_object* v_subgoals_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
lean_dec_ref(v___x_5328_);
v_mvarIds_5333_ = lean_ctor_get(v_a_5332_, 0);
lean_inc(v_mvarIds_5333_);
lean_dec_ref_known(v_a_5332_, 1);
v_frame_5334_ = lean_ctor_get(v_split_5308_, 0);
lean_inc_ref(v_frame_5334_);
v_residualPre_5335_ = lean_ctor_get(v_split_5308_, 1);
lean_inc(v_residualPre_5335_);
v_splitVCProof_5336_ = lean_ctor_get(v_split_5308_, 2);
lean_inc_ref(v_splitVCProof_5336_);
v_subgoals_5337_ = lean_ctor_get(v_split_5308_, 3);
lean_inc(v_subgoals_5337_);
lean_dec_ref(v_split_5308_);
v___x_5338_ = lean_box(0);
v___x_5339_ = lean_array_mk(v_mvarIds_5333_);
v___x_5340_ = lean_array_get(v___x_5338_, v___x_5339_, v_frameIdx_5325_);
lean_dec(v_frameIdx_5325_);
v___x_5341_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5340_, v_frame_5334_, v_a_5317_);
lean_dec_ref(v___x_5341_);
v___x_5342_ = lean_array_get(v___x_5338_, v___x_5339_, v_splitVCIdx_5324_);
lean_dec(v_splitVCIdx_5324_);
lean_inc(v___x_5342_);
v___x_5343_ = l_Lean_MVarId_getType(v___x_5342_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; lean_object* v___y_5346_; lean_object* v___y_5347_; lean_object* v___y_5348_; lean_object* v___y_5349_; lean_object* v___x_5354_; uint8_t v___x_5355_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
lean_inc_n(v_a_5344_, 2);
lean_dec_ref_known(v___x_5343_, 1);
v___x_5354_ = l_Lean_Expr_cleanupAnnotations(v_a_5344_);
v___x_5355_ = l_Lean_Expr_isApp(v___x_5354_);
if (v___x_5355_ == 0)
{
lean_dec_ref(v___x_5354_);
lean_dec(v___x_5342_);
lean_dec_ref(v___x_5339_);
lean_dec(v_subgoals_5337_);
lean_dec_ref(v_splitVCProof_5336_);
lean_dec(v_residualPre_5335_);
lean_dec_ref(v_info_5306_);
v___y_5346_ = v_a_5316_;
v___y_5347_ = v_a_5317_;
v___y_5348_ = v_a_5318_;
v___y_5349_ = v_a_5319_;
goto v___jp_5345_;
}
else
{
lean_object* v_arg_5356_; lean_object* v___x_5357_; uint8_t v___x_5358_; 
v_arg_5356_ = lean_ctor_get(v___x_5354_, 1);
lean_inc_ref(v_arg_5356_);
v___x_5357_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5354_);
v___x_5358_ = l_Lean_Expr_isApp(v___x_5357_);
if (v___x_5358_ == 0)
{
lean_dec_ref(v___x_5357_);
lean_dec_ref(v_arg_5356_);
lean_dec(v___x_5342_);
lean_dec_ref(v___x_5339_);
lean_dec(v_subgoals_5337_);
lean_dec_ref(v_splitVCProof_5336_);
lean_dec(v_residualPre_5335_);
lean_dec_ref(v_info_5306_);
v___y_5346_ = v_a_5316_;
v___y_5347_ = v_a_5317_;
v___y_5348_ = v_a_5318_;
v___y_5349_ = v_a_5319_;
goto v___jp_5345_;
}
else
{
lean_object* v___x_5359_; uint8_t v___x_5360_; 
v___x_5359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5357_);
v___x_5360_ = l_Lean_Expr_isApp(v___x_5359_);
if (v___x_5360_ == 0)
{
lean_dec_ref(v___x_5359_);
lean_dec_ref(v_arg_5356_);
lean_dec(v___x_5342_);
lean_dec_ref(v___x_5339_);
lean_dec(v_subgoals_5337_);
lean_dec_ref(v_splitVCProof_5336_);
lean_dec(v_residualPre_5335_);
lean_dec_ref(v_info_5306_);
v___y_5346_ = v_a_5316_;
v___y_5347_ = v_a_5317_;
v___y_5348_ = v_a_5318_;
v___y_5349_ = v_a_5319_;
goto v___jp_5345_;
}
else
{
lean_object* v___x_5361_; uint8_t v___x_5362_; 
v___x_5361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5359_);
v___x_5362_ = l_Lean_Expr_isApp(v___x_5361_);
if (v___x_5362_ == 0)
{
lean_dec_ref(v___x_5361_);
lean_dec_ref(v_arg_5356_);
lean_dec(v___x_5342_);
lean_dec_ref(v___x_5339_);
lean_dec(v_subgoals_5337_);
lean_dec_ref(v_splitVCProof_5336_);
lean_dec(v_residualPre_5335_);
lean_dec_ref(v_info_5306_);
v___y_5346_ = v_a_5316_;
v___y_5347_ = v_a_5317_;
v___y_5348_ = v_a_5318_;
v___y_5349_ = v_a_5319_;
goto v___jp_5345_;
}
else
{
lean_object* v___x_5363_; lean_object* v___x_5364_; uint8_t v___x_5365_; 
v___x_5363_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5361_);
v___x_5364_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5365_ = l_Lean_Expr_isConstOf(v___x_5363_, v___x_5364_);
lean_dec_ref(v___x_5363_);
if (v___x_5365_ == 0)
{
lean_dec_ref(v_arg_5356_);
lean_dec(v___x_5342_);
lean_dec_ref(v___x_5339_);
lean_dec(v_subgoals_5337_);
lean_dec_ref(v_splitVCProof_5336_);
lean_dec(v_residualPre_5335_);
lean_dec_ref(v_info_5306_);
v___y_5346_ = v_a_5316_;
v___y_5347_ = v_a_5317_;
v___y_5348_ = v_a_5318_;
v___y_5349_ = v_a_5319_;
goto v___jp_5345_;
}
else
{
lean_object* v_excessArgs_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5373_; uint8_t v_isShared_5374_; uint8_t v_isSharedCheck_5380_; 
lean_dec(v_a_5344_);
v_excessArgs_5366_ = lean_ctor_get(v_info_5306_, 2);
lean_inc_ref(v_excessArgs_5366_);
lean_dec_ref(v_info_5306_);
v___x_5367_ = lean_array_get_size(v_excessArgs_5366_);
lean_dec_ref(v_excessArgs_5366_);
v___x_5368_ = l_Lean_Expr_stripArgsN(v_arg_5356_, v___x_5367_);
lean_dec_ref(v_arg_5356_);
v___x_5369_ = l_Lean_Expr_appArg_x21(v___x_5368_);
lean_dec_ref(v___x_5368_);
v___x_5370_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_residualPre_5335_, v___x_5369_, v_a_5317_);
lean_dec_ref(v___x_5370_);
v___x_5371_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v___x_5342_, v_splitVCProof_5336_, v_a_5317_);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5380_ == 0)
{
lean_object* v_unused_5381_; 
v_unused_5381_ = lean_ctor_get(v___x_5371_, 0);
lean_dec(v_unused_5381_);
v___x_5373_ = v___x_5371_;
v_isShared_5374_ = v_isSharedCheck_5380_;
goto v_resetjp_5372_;
}
else
{
lean_dec(v___x_5371_);
v___x_5373_ = lean_box(0);
v_isShared_5374_ = v_isSharedCheck_5380_;
goto v_resetjp_5372_;
}
v_resetjp_5372_:
{
lean_object* v___x_5375_; lean_object* v___x_5376_; lean_object* v___x_5378_; 
v___x_5375_ = lean_array_to_list(v___x_5339_);
v___x_5376_ = l_List_appendTR___redArg(v___x_5375_, v_subgoals_5337_);
if (v_isShared_5374_ == 0)
{
lean_ctor_set(v___x_5373_, 0, v___x_5376_);
v___x_5378_ = v___x_5373_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v___x_5376_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
}
}
}
v___jp_5345_:
{
lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v___x_5350_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3);
v___x_5351_ = l_Lean_indentExpr(v_a_5344_);
v___x_5352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5352_, 0, v___x_5350_);
lean_ctor_set(v___x_5352_, 1, v___x_5351_);
v___x_5353_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5352_, v___y_5346_, v___y_5347_, v___y_5348_, v___y_5349_);
return v___x_5353_;
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec(v___x_5342_);
lean_dec_ref(v___x_5339_);
lean_dec(v_subgoals_5337_);
lean_dec_ref(v_splitVCProof_5336_);
lean_dec(v_residualPre_5335_);
lean_dec_ref(v_info_5306_);
v_a_5382_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5343_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5343_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
else
{
lean_object* v___x_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; 
lean_dec(v_a_5332_);
lean_dec(v_frameIdx_5325_);
lean_dec(v_splitVCIdx_5324_);
lean_dec_ref(v_split_5308_);
lean_dec_ref(v_info_5306_);
v___x_5390_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__5);
v___x_5391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5391_, 0, v___x_5390_);
lean_ctor_set(v___x_5391_, 1, v___x_5328_);
v___x_5392_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5391_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
return v___x_5392_;
}
}
else
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
lean_dec_ref(v___x_5328_);
lean_dec(v_frameIdx_5325_);
lean_dec(v_splitVCIdx_5324_);
lean_dec_ref(v_split_5308_);
lean_dec_ref(v_info_5306_);
v_a_5393_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5331_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5331_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
}
else
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5408_; 
lean_dec_ref(v_split_5308_);
lean_dec_ref(v_info_5306_);
lean_dec(v_goal_5305_);
v_a_5401_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5403_ = v___x_5321_;
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v___x_5321_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
return v___x_5406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___boxed(lean_object* v_goal_5409_, lean_object* v_info_5410_, lean_object* v_fp_5411_, lean_object* v_split_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_){
_start:
{
lean_object* v_res_5425_; 
v_res_5425_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5409_, v_info_5410_, v_fp_5411_, v_split_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_, v_a_5420_, v_a_5421_, v_a_5422_, v_a_5423_);
lean_dec(v_a_5423_);
lean_dec_ref(v_a_5422_);
lean_dec(v_a_5421_);
lean_dec_ref(v_a_5420_);
lean_dec(v_a_5419_);
lean_dec_ref(v_a_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
lean_dec(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
return v_res_5425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(lean_object* v_mkOpAppM_5426_, lean_object* v_info_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v___x_5435_; 
lean_inc(v___y_5433_);
lean_inc_ref(v___y_5432_);
lean_inc(v___y_5431_);
lean_inc_ref(v___y_5430_);
v___x_5435_ = lean_apply_6(v_mkOpAppM_5426_, v_info_5427_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, lean_box(0));
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref_known(v___x_5435_, 1);
v___x_5437_ = l_Lean_Meta_Sym_shareCommon(v_a_5436_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_);
return v___x_5437_;
}
else
{
return v___x_5435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed(lean_object* v_mkOpAppM_5438_, lean_object* v_info_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_){
_start:
{
lean_object* v_res_5447_; 
v_res_5447_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0(v_mkOpAppM_5438_, v_info_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_, v___y_5444_, v___y_5445_);
lean_dec(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg(lean_object* v_a_5448_, lean_object* v_x_5449_){
_start:
{
if (lean_obj_tag(v_x_5449_) == 0)
{
lean_object* v___x_5450_; 
v___x_5450_ = lean_box(0);
return v___x_5450_;
}
else
{
lean_object* v_key_5451_; lean_object* v_value_5452_; lean_object* v_tail_5453_; uint8_t v___x_5454_; 
v_key_5451_ = lean_ctor_get(v_x_5449_, 0);
v_value_5452_ = lean_ctor_get(v_x_5449_, 1);
v_tail_5453_ = lean_ctor_get(v_x_5449_, 2);
v___x_5454_ = lean_name_eq(v_key_5451_, v_a_5448_);
if (v___x_5454_ == 0)
{
v_x_5449_ = v_tail_5453_;
goto _start;
}
else
{
lean_object* v___x_5456_; 
lean_inc(v_value_5452_);
v___x_5456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5456_, 0, v_value_5452_);
return v___x_5456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg___boxed(lean_object* v_a_5457_, lean_object* v_x_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg(v_a_5457_, v_x_5458_);
lean_dec(v_x_5458_);
lean_dec(v_a_5457_);
return v_res_5459_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5460_; uint64_t v___x_5461_; 
v___x_5460_ = lean_unsigned_to_nat(1723u);
v___x_5461_ = lean_uint64_of_nat(v___x_5460_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg(lean_object* v_m_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v_buckets_5464_; lean_object* v___x_5465_; uint64_t v___y_5467_; 
v_buckets_5464_ = lean_ctor_get(v_m_5462_, 1);
v___x_5465_ = lean_array_get_size(v_buckets_5464_);
if (lean_obj_tag(v_a_5463_) == 0)
{
uint64_t v___x_5481_; 
v___x_5481_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___closed__0);
v___y_5467_ = v___x_5481_;
goto v___jp_5466_;
}
else
{
uint64_t v_hash_5482_; 
v_hash_5482_ = lean_ctor_get_uint64(v_a_5463_, sizeof(void*)*2);
v___y_5467_ = v_hash_5482_;
goto v___jp_5466_;
}
v___jp_5466_:
{
uint64_t v___x_5468_; uint64_t v___x_5469_; uint64_t v_fold_5470_; uint64_t v___x_5471_; uint64_t v___x_5472_; uint64_t v___x_5473_; size_t v___x_5474_; size_t v___x_5475_; size_t v___x_5476_; size_t v___x_5477_; size_t v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; 
v___x_5468_ = 32ULL;
v___x_5469_ = lean_uint64_shift_right(v___y_5467_, v___x_5468_);
v_fold_5470_ = lean_uint64_xor(v___y_5467_, v___x_5469_);
v___x_5471_ = 16ULL;
v___x_5472_ = lean_uint64_shift_right(v_fold_5470_, v___x_5471_);
v___x_5473_ = lean_uint64_xor(v_fold_5470_, v___x_5472_);
v___x_5474_ = lean_uint64_to_usize(v___x_5473_);
v___x_5475_ = lean_usize_of_nat(v___x_5465_);
v___x_5476_ = ((size_t)1ULL);
v___x_5477_ = lean_usize_sub(v___x_5475_, v___x_5476_);
v___x_5478_ = lean_usize_land(v___x_5474_, v___x_5477_);
v___x_5479_ = lean_array_uget_borrowed(v_buckets_5464_, v___x_5478_);
v___x_5480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg(v_a_5463_, v___x_5479_);
return v___x_5480_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg___boxed(lean_object* v_m_5483_, lean_object* v_a_5484_){
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg(v_m_5483_, v_a_5484_);
lean_dec(v_a_5484_);
lean_dec_ref(v_m_5483_);
return v_res_5485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__0));
v___x_5488_ = l_Lean_stringToMessageData(v___x_5487_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1(lean_object* v_scope_5489_, lean_object* v_goal_5490_, lean_object* v_info_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v___x_5504_; 
lean_inc_ref(v_info_5491_);
lean_inc(v_goal_5490_);
v___x_5504_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_compileSpecRule(v_scope_5489_, v_goal_5490_, v_info_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v_a_5505_; lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5640_; 
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5640_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5507_ = v___x_5504_;
v_isShared_5508_ = v_isSharedCheck_5640_;
goto v_resetjp_5506_;
}
else
{
lean_inc(v_a_5505_);
lean_dec(v___x_5504_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5640_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
if (lean_obj_tag(v_a_5505_) == 0)
{
lean_object* v_a_5509_; lean_object* v___x_5511_; 
lean_dec_ref(v_info_5491_);
lean_dec(v_goal_5490_);
v_a_5509_ = lean_ctor_get(v_a_5505_, 0);
lean_inc(v_a_5509_);
lean_dec_ref_known(v_a_5505_, 1);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 0, v_a_5509_);
v___x_5511_ = v___x_5507_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5509_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
else
{
lean_object* v_a_5513_; lean_object* v_fst_5514_; lean_object* v_snd_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5639_; 
lean_del_object(v___x_5507_);
v_a_5513_ = lean_ctor_get(v_a_5505_, 0);
lean_inc(v_a_5513_);
lean_dec_ref_known(v_a_5505_, 1);
v_fst_5514_ = lean_ctor_get(v_a_5513_, 0);
v_snd_5515_ = lean_ctor_get(v_a_5513_, 1);
v_isSharedCheck_5639_ = !lean_is_exclusive(v_a_5513_);
if (v_isSharedCheck_5639_ == 0)
{
v___x_5517_ = v_a_5513_;
v_isShared_5518_ = v_isSharedCheck_5639_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_snd_5515_);
lean_inc(v_fst_5514_);
lean_dec(v_a_5513_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5639_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___y_5520_; lean_object* v___y_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v___y_5532_; lean_object* v_fst_5563_; lean_object* v_snd_5564_; lean_object* v___x_5566_; uint8_t v_isShared_5567_; uint8_t v_isSharedCheck_5638_; 
v_fst_5563_ = lean_ctor_get(v_snd_5515_, 0);
v_snd_5564_ = lean_ctor_get(v_snd_5515_, 1);
v_isSharedCheck_5638_ = !lean_is_exclusive(v_snd_5515_);
if (v_isSharedCheck_5638_ == 0)
{
v___x_5566_ = v_snd_5515_;
v_isShared_5567_ = v_isSharedCheck_5638_;
goto v_resetjp_5565_;
}
else
{
lean_inc(v_snd_5564_);
lean_inc(v_fst_5563_);
lean_dec(v_snd_5515_);
v___x_5566_ = lean_box(0);
v_isShared_5567_ = v_isSharedCheck_5638_;
goto v_resetjp_5565_;
}
v___jp_5519_:
{
lean_object* v___x_5533_; 
v___x_5533_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_FrameSplit_instantiateMVarsS(v___y_5520_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
if (lean_obj_tag(v___x_5533_) == 0)
{
lean_object* v_a_5534_; lean_object* v___x_5535_; 
v_a_5534_ = lean_ctor_get(v___x_5533_, 0);
lean_inc(v_a_5534_);
lean_dec_ref_known(v___x_5533_, 1);
v___x_5535_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5490_, v_info_5491_, v___y_5521_, v_a_5534_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5546_; 
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5538_ = v___x_5535_;
v_isShared_5539_ = v_isSharedCheck_5546_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5535_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5546_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 1, v_a_5536_);
v___x_5541_ = v___x_5517_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_fst_5514_);
lean_ctor_set(v_reuseFailAlloc_5545_, 1, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5543_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 0, v___x_5541_);
v___x_5543_ = v___x_5538_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5541_);
v___x_5543_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
return v___x_5543_;
}
}
}
}
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_del_object(v___x_5517_);
lean_dec(v_fst_5514_);
v_a_5547_ = lean_ctor_get(v___x_5535_, 0);
v_isSharedCheck_5554_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5554_ == 0)
{
v___x_5549_ = v___x_5535_;
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_a_5547_);
lean_dec(v___x_5535_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5554_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5552_; 
if (v_isShared_5550_ == 0)
{
v___x_5552_ = v___x_5549_;
goto v_reusejp_5551_;
}
else
{
lean_object* v_reuseFailAlloc_5553_; 
v_reuseFailAlloc_5553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5553_, 0, v_a_5547_);
v___x_5552_ = v_reuseFailAlloc_5553_;
goto v_reusejp_5551_;
}
v_reusejp_5551_:
{
return v___x_5552_;
}
}
}
}
else
{
lean_object* v_a_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
lean_dec_ref(v___y_5521_);
lean_del_object(v___x_5517_);
lean_dec(v_fst_5514_);
lean_dec_ref(v_info_5491_);
lean_dec(v_goal_5490_);
v_a_5555_ = lean_ctor_get(v___x_5533_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5533_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5557_ = v___x_5533_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_a_5555_);
lean_dec(v___x_5533_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5555_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
v_resetjp_5565_:
{
lean_object* v___y_5569_; uint8_t v_conjunctivePre_5626_; 
v_conjunctivePre_5626_ = lean_ctor_get_uint8(v_fst_5563_, sizeof(void*)*4);
if (v_conjunctivePre_5626_ == 0)
{
lean_object* v___x_5627_; uint8_t v___x_5628_; 
v___x_5627_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(v_info_5491_);
v___x_5628_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(v___x_5627_);
if (v___x_5628_ == 0)
{
lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5629_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_5491_);
v___x_5630_ = l_Lean_Expr_getAppFn(v___x_5629_);
lean_dec_ref(v___x_5629_);
v___x_5631_ = l_Lean_Expr_constName_x3f(v___x_5630_);
lean_dec_ref(v___x_5630_);
if (lean_obj_tag(v___x_5631_) == 0)
{
goto v___jp_5624_;
}
else
{
lean_object* v_val_5632_; lean_object* v_frameProcs_5633_; lean_object* v___x_5634_; 
v_val_5632_ = lean_ctor_get(v___x_5631_, 0);
lean_inc(v_val_5632_);
lean_dec_ref_known(v___x_5631_, 1);
v_frameProcs_5633_ = lean_ctor_get(v___y_5492_, 1);
v___x_5634_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg(v_frameProcs_5633_, v_val_5632_);
lean_dec(v_val_5632_);
if (lean_obj_tag(v___x_5634_) == 0)
{
goto v___jp_5624_;
}
else
{
lean_object* v_val_5635_; 
v_val_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc(v_val_5635_);
lean_dec_ref_known(v___x_5634_, 1);
v___y_5569_ = v_val_5635_;
goto v___jp_5568_;
}
}
}
else
{
lean_object* v___x_5636_; 
lean_del_object(v___x_5566_);
lean_del_object(v___x_5517_);
v___x_5636_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule(v_fst_5514_, v_goal_5490_, v_info_5491_, v_fst_5563_, v_snd_5564_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
return v___x_5636_;
}
}
else
{
lean_object* v___x_5637_; 
lean_del_object(v___x_5566_);
lean_del_object(v___x_5517_);
v___x_5637_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule(v_fst_5514_, v_goal_5490_, v_info_5491_, v_fst_5563_, v_snd_5564_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
return v___x_5637_;
}
v___jp_5568_:
{
lean_object* v___x_5570_; 
lean_inc_ref(v_info_5491_);
lean_inc_ref(v___y_5569_);
v___x_5570_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v___y_5569_, v_info_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; lean_object* v_mkOpAppM_5572_; lean_object* v_proc_5573_; lean_object* v___x_5574_; lean_object* v___f_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_a_5571_);
lean_dec_ref_known(v___x_5570_, 1);
v_mkOpAppM_5572_ = lean_ctor_get(v___y_5569_, 2);
v_proc_5573_ = lean_ctor_get(v___y_5569_, 4);
lean_inc(v_fst_5563_);
v___x_5574_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorem_global_x3f(v_fst_5563_);
lean_inc_ref_n(v_info_5491_, 2);
lean_inc_ref(v_mkOpAppM_5572_);
v___f_5575_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5575_, 0, v_mkOpAppM_5572_);
lean_closure_set(v___f_5575_, 1, v_info_5491_);
lean_inc(v_snd_5564_);
lean_inc(v_goal_5490_);
v___x_5576_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5576_, 0, v_info_5491_);
lean_ctor_set(v___x_5576_, 1, v_goal_5490_);
lean_ctor_set(v___x_5576_, 2, v_a_5571_);
lean_ctor_set(v___x_5576_, 3, v___x_5574_);
lean_ctor_set(v___x_5576_, 4, v_snd_5564_);
lean_ctor_set(v___x_5576_, 5, v___f_5575_);
lean_inc_ref(v_proc_5573_);
lean_inc(v___y_5502_);
lean_inc_ref(v___y_5501_);
lean_inc(v___y_5500_);
lean_inc_ref(v___y_5499_);
lean_inc(v___y_5498_);
lean_inc_ref(v___y_5497_);
v___x_5577_ = lean_apply_8(v_proc_5573_, v___x_5576_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, lean_box(0));
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref_known(v___x_5577_, 1);
if (lean_obj_tag(v_a_5578_) == 0)
{
lean_object* v___x_5579_; 
lean_dec_ref(v___y_5569_);
lean_del_object(v___x_5566_);
lean_del_object(v___x_5517_);
v___x_5579_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpecRule(v_fst_5514_, v_goal_5490_, v_info_5491_, v_fst_5563_, v_snd_5564_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
return v___x_5579_;
}
else
{
lean_object* v_options_5580_; uint8_t v_hasTrace_5581_; 
lean_dec(v_snd_5564_);
lean_dec(v_fst_5563_);
v_options_5580_ = lean_ctor_get(v___y_5501_, 2);
v_hasTrace_5581_ = lean_ctor_get_uint8(v_options_5580_, sizeof(void*)*1);
if (v_hasTrace_5581_ == 0)
{
lean_object* v_val_5582_; 
lean_del_object(v___x_5566_);
v_val_5582_ = lean_ctor_get(v_a_5578_, 0);
lean_inc(v_val_5582_);
lean_dec_ref_known(v_a_5578_, 1);
v___y_5520_ = v_val_5582_;
v___y_5521_ = v___y_5569_;
v___y_5522_ = v___y_5492_;
v___y_5523_ = v___y_5493_;
v___y_5524_ = v___y_5494_;
v___y_5525_ = v___y_5495_;
v___y_5526_ = v___y_5496_;
v___y_5527_ = v___y_5497_;
v___y_5528_ = v___y_5498_;
v___y_5529_ = v___y_5499_;
v___y_5530_ = v___y_5500_;
v___y_5531_ = v___y_5501_;
v___y_5532_ = v___y_5502_;
goto v___jp_5519_;
}
else
{
lean_object* v_val_5583_; lean_object* v_inheritedTraceOptions_5584_; lean_object* v___x_5585_; lean_object* v___x_5586_; uint8_t v___x_5587_; 
v_val_5583_ = lean_ctor_get(v_a_5578_, 0);
lean_inc(v_val_5583_);
lean_dec_ref_known(v_a_5578_, 1);
v_inheritedTraceOptions_5584_ = lean_ctor_get(v___y_5501_, 13);
v___x_5585_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_5586_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5584_, v_options_5580_, v___x_5586_);
if (v___x_5587_ == 0)
{
lean_del_object(v___x_5566_);
v___y_5520_ = v_val_5583_;
v___y_5521_ = v___y_5569_;
v___y_5522_ = v___y_5492_;
v___y_5523_ = v___y_5493_;
v___y_5524_ = v___y_5494_;
v___y_5525_ = v___y_5495_;
v___y_5526_ = v___y_5496_;
v___y_5527_ = v___y_5497_;
v___y_5528_ = v___y_5498_;
v___y_5529_ = v___y_5499_;
v___y_5530_ = v___y_5500_;
v___y_5531_ = v___y_5501_;
v___y_5532_ = v___y_5502_;
goto v___jp_5519_;
}
else
{
lean_object* v_frame_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5593_; 
v_frame_5588_ = lean_ctor_get(v_val_5583_, 0);
v___x_5589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___closed__1);
v___x_5590_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_5491_);
v___x_5591_ = l_Lean_MessageData_ofExpr(v___x_5590_);
if (v_isShared_5567_ == 0)
{
lean_ctor_set_tag(v___x_5566_, 7);
lean_ctor_set(v___x_5566_, 1, v___x_5591_);
lean_ctor_set(v___x_5566_, 0, v___x_5589_);
v___x_5593_ = v___x_5566_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5607_, 1, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; 
v___x_5594_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3);
v___x_5595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5595_, 0, v___x_5593_);
lean_ctor_set(v___x_5595_, 1, v___x_5594_);
lean_inc_ref(v_frame_5588_);
v___x_5596_ = l_Lean_indentExpr(v_frame_5588_);
v___x_5597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5597_, 0, v___x_5595_);
lean_ctor_set(v___x_5597_, 1, v___x_5596_);
v___x_5598_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5585_, v___x_5597_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_);
if (lean_obj_tag(v___x_5598_) == 0)
{
lean_dec_ref_known(v___x_5598_, 1);
v___y_5520_ = v_val_5583_;
v___y_5521_ = v___y_5569_;
v___y_5522_ = v___y_5492_;
v___y_5523_ = v___y_5493_;
v___y_5524_ = v___y_5494_;
v___y_5525_ = v___y_5495_;
v___y_5526_ = v___y_5496_;
v___y_5527_ = v___y_5497_;
v___y_5528_ = v___y_5498_;
v___y_5529_ = v___y_5499_;
v___y_5530_ = v___y_5500_;
v___y_5531_ = v___y_5501_;
v___y_5532_ = v___y_5502_;
goto v___jp_5519_;
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5606_; 
lean_dec(v_val_5583_);
lean_dec_ref(v___y_5569_);
lean_del_object(v___x_5517_);
lean_dec(v_fst_5514_);
lean_dec_ref(v_info_5491_);
lean_dec(v_goal_5490_);
v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5598_);
if (v_isSharedCheck_5606_ == 0)
{
v___x_5601_ = v___x_5598_;
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5598_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5606_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
lean_object* v___x_5604_; 
if (v_isShared_5602_ == 0)
{
v___x_5604_ = v___x_5601_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_a_5599_);
v___x_5604_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
return v___x_5604_;
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
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5615_; 
lean_dec_ref(v___y_5569_);
lean_del_object(v___x_5566_);
lean_dec(v_snd_5564_);
lean_dec(v_fst_5563_);
lean_del_object(v___x_5517_);
lean_dec(v_fst_5514_);
lean_dec_ref(v_info_5491_);
lean_dec(v_goal_5490_);
v_a_5608_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5615_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5610_ = v___x_5577_;
v_isShared_5611_ = v_isSharedCheck_5615_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5577_);
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
else
{
lean_object* v_a_5616_; lean_object* v___x_5618_; uint8_t v_isShared_5619_; uint8_t v_isSharedCheck_5623_; 
lean_dec_ref(v___y_5569_);
lean_del_object(v___x_5566_);
lean_dec(v_snd_5564_);
lean_dec(v_fst_5563_);
lean_del_object(v___x_5517_);
lean_dec(v_fst_5514_);
lean_dec_ref(v_info_5491_);
lean_dec(v_goal_5490_);
v_a_5616_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5618_ = v___x_5570_;
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
else
{
lean_inc(v_a_5616_);
lean_dec(v___x_5570_);
v___x_5618_ = lean_box(0);
v_isShared_5619_ = v_isSharedCheck_5623_;
goto v_resetjp_5617_;
}
v_resetjp_5617_:
{
lean_object* v___x_5621_; 
if (v_isShared_5619_ == 0)
{
v___x_5621_ = v___x_5618_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5616_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
}
v___jp_5624_:
{
lean_object* v___x_5625_; 
v___x_5625_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc;
v___y_5569_ = v___x_5625_;
goto v___jp_5568_;
}
}
}
}
}
}
else
{
lean_object* v_a_5641_; lean_object* v___x_5643_; uint8_t v_isShared_5644_; uint8_t v_isSharedCheck_5648_; 
lean_dec_ref(v_info_5491_);
lean_dec(v_goal_5490_);
v_a_5641_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5648_ == 0)
{
v___x_5643_ = v___x_5504_;
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
else
{
lean_inc(v_a_5641_);
lean_dec(v___x_5504_);
v___x_5643_ = lean_box(0);
v_isShared_5644_ = v_isSharedCheck_5648_;
goto v_resetjp_5642_;
}
v_resetjp_5642_:
{
lean_object* v___x_5646_; 
if (v_isShared_5644_ == 0)
{
v___x_5646_ = v___x_5643_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_a_5641_);
v___x_5646_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
return v___x_5646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___boxed(lean_object* v_scope_5649_, lean_object* v_goal_5650_, lean_object* v_info_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v_res_5664_; 
v_res_5664_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1(v_scope_5649_, v_goal_5650_, v_info_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
return v_res_5664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_scope_5665_, lean_object* v_goal_5666_, lean_object* v_info_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_, lean_object* v_a_5671_, lean_object* v_a_5672_, lean_object* v_a_5673_, lean_object* v_a_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_){
_start:
{
lean_object* v___f_5680_; lean_object* v___x_5681_; 
lean_inc(v_goal_5666_);
v___f_5680_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___lam__1___boxed), 15, 3);
lean_closure_set(v___f_5680_, 0, v_scope_5665_);
lean_closure_set(v___f_5680_, 1, v_goal_5666_);
lean_closure_set(v___f_5680_, 2, v_info_5667_);
v___x_5681_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5666_, v___f_5680_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_, v_a_5673_, v_a_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_);
return v___x_5681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object* v_scope_5682_, lean_object* v_goal_5683_, lean_object* v_info_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_, lean_object* v_a_5689_, lean_object* v_a_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_5682_, v_goal_5683_, v_info_5684_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_, v_a_5689_, v_a_5690_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
lean_dec(v_a_5695_);
lean_dec_ref(v_a_5694_);
lean_dec(v_a_5693_);
lean_dec_ref(v_a_5692_);
lean_dec(v_a_5691_);
lean_dec_ref(v_a_5690_);
lean_dec(v_a_5689_);
lean_dec_ref(v_a_5688_);
lean_dec(v_a_5687_);
lean_dec(v_a_5686_);
lean_dec_ref(v_a_5685_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_00_u03b2_5698_, lean_object* v_m_5699_, lean_object* v_a_5700_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___redArg(v_m_5699_, v_a_5700_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0___boxed(lean_object* v_00_u03b2_5702_, lean_object* v_m_5703_, lean_object* v_a_5704_){
_start:
{
lean_object* v_res_5705_; 
v_res_5705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v_00_u03b2_5702_, v_m_5703_, v_a_5704_);
lean_dec(v_a_5704_);
lean_dec_ref(v_m_5703_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0(lean_object* v_00_u03b2_5706_, lean_object* v_a_5707_, lean_object* v_x_5708_){
_start:
{
lean_object* v___x_5709_; 
v___x_5709_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___redArg(v_a_5707_, v_x_5708_);
return v___x_5709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5710_, lean_object* v_a_5711_, lean_object* v_x_5712_){
_start:
{
lean_object* v_res_5713_; 
v_res_5713_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0_spec__0(v_00_u03b2_5710_, v_a_5711_, v_x_5712_);
lean_dec(v_x_5712_);
lean_dec(v_a_5711_);
return v_res_5713_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5715_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_5716_ = l_Lean_stringToMessageData(v___x_5715_);
return v___x_5716_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5718_; lean_object* v___x_5719_; 
v___x_5718_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2));
v___x_5719_ = l_Lean_stringToMessageData(v___x_5718_);
return v___x_5719_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5721_; lean_object* v___x_5722_; 
v___x_5721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_5722_ = l_Lean_stringToMessageData(v___x_5721_);
return v___x_5722_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5724_; lean_object* v___x_5725_; 
v___x_5724_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6));
v___x_5725_ = l_Lean_stringToMessageData(v___x_5724_);
return v___x_5725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_5728_, lean_object* v_scope_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_){
_start:
{
lean_object* v_gs_5743_; lean_object* v_g_5747_; lean_object* v___y_5753_; lean_object* v___y_5754_; lean_object* v___y_5759_; lean_object* v_g_5760_; lean_object* v___y_5766_; lean_object* v_gs_5767_; lean_object* v___y_5771_; lean_object* v_g_5772_; lean_object* v___y_5773_; lean_object* v___y_5795_; lean_object* v___y_5796_; lean_object* v___y_5797_; lean_object* v___y_5798_; lean_object* v___y_5799_; lean_object* v___y_5800_; lean_object* v___y_5801_; lean_object* v___y_5802_; lean_object* v___y_5803_; lean_object* v___y_5804_; lean_object* v___y_5805_; lean_object* v___y_5806_; lean_object* v___y_5807_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; lean_object* v___y_5828_; lean_object* v___y_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___y_5833_; lean_object* v___x_5946_; 
v___x_5946_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_5731_);
if (lean_obj_tag(v___x_5946_) == 0)
{
lean_object* v_a_5947_; lean_object* v___x_5949_; uint8_t v_isShared_5950_; uint8_t v_isSharedCheck_6211_; 
v_a_5947_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_6211_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_6211_ == 0)
{
v___x_5949_ = v___x_5946_;
v_isShared_5950_ = v_isSharedCheck_6211_;
goto v_resetjp_5948_;
}
else
{
lean_inc(v_a_5947_);
lean_dec(v___x_5946_);
v___x_5949_ = lean_box(0);
v_isShared_5950_ = v_isSharedCheck_6211_;
goto v_resetjp_5948_;
}
v_resetjp_5948_:
{
uint8_t v___x_5951_; 
v___x_5951_ = lean_unbox(v_a_5947_);
lean_dec(v_a_5947_);
if (v___x_5951_ == 0)
{
lean_object* v___x_5952_; 
lean_del_object(v___x_5949_);
lean_inc(v_goal_5728_);
v___x_5952_ = l_Lean_MVarId_getType(v_goal_5728_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
if (lean_obj_tag(v___x_5952_) == 0)
{
lean_object* v_a_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_6198_; 
v_a_5953_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_6198_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_6198_ == 0)
{
v___x_5955_ = v___x_5952_;
v_isShared_5956_ = v_isSharedCheck_6198_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_a_5953_);
lean_dec(v___x_5952_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_6198_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v_options_5963_; lean_object* v_inheritedTraceOptions_5964_; uint8_t v_hasTrace_5965_; lean_object* v___x_5966_; lean_object* v___y_5968_; lean_object* v___y_5969_; lean_object* v___y_5970_; lean_object* v___y_5971_; lean_object* v___y_5972_; lean_object* v___y_5973_; lean_object* v___y_5974_; lean_object* v___y_5975_; lean_object* v___y_5976_; lean_object* v___y_5977_; lean_object* v___y_5978_; 
v_options_5963_ = lean_ctor_get(v___y_5739_, 2);
v_inheritedTraceOptions_5964_ = lean_ctor_get(v___y_5739_, 13);
v_hasTrace_5965_ = lean_ctor_get_uint8(v_options_5963_, sizeof(void*)*1);
v___x_5966_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_5965_ == 0)
{
v___y_5968_ = v___y_5730_;
v___y_5969_ = v___y_5731_;
v___y_5970_ = v___y_5732_;
v___y_5971_ = v___y_5733_;
v___y_5972_ = v___y_5734_;
v___y_5973_ = v___y_5735_;
v___y_5974_ = v___y_5736_;
v___y_5975_ = v___y_5737_;
v___y_5976_ = v___y_5738_;
v___y_5977_ = v___y_5739_;
v___y_5978_ = v___y_5740_;
goto v___jp_5967_;
}
else
{
lean_object* v___x_6184_; uint8_t v___x_6185_; 
v___x_6184_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_6185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5964_, v_options_5963_, v___x_6184_);
if (v___x_6185_ == 0)
{
v___y_5968_ = v___y_5730_;
v___y_5969_ = v___y_5731_;
v___y_5970_ = v___y_5732_;
v___y_5971_ = v___y_5733_;
v___y_5972_ = v___y_5734_;
v___y_5973_ = v___y_5735_;
v___y_5974_ = v___y_5736_;
v___y_5975_ = v___y_5737_;
v___y_5976_ = v___y_5738_;
v___y_5977_ = v___y_5739_;
v___y_5978_ = v___y_5740_;
goto v___jp_5967_;
}
else
{
lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; 
v___x_6186_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_5953_);
v___x_6187_ = l_Lean_MessageData_ofExpr(v_a_5953_);
v___x_6188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6188_, 0, v___x_6186_);
lean_ctor_set(v___x_6188_, 1, v___x_6187_);
v___x_6189_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5966_, v___x_6188_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
if (lean_obj_tag(v___x_6189_) == 0)
{
lean_dec_ref_known(v___x_6189_, 1);
v___y_5968_ = v___y_5730_;
v___y_5969_ = v___y_5731_;
v___y_5970_ = v___y_5732_;
v___y_5971_ = v___y_5733_;
v___y_5972_ = v___y_5734_;
v___y_5973_ = v___y_5735_;
v___y_5974_ = v___y_5736_;
v___y_5975_ = v___y_5737_;
v___y_5976_ = v___y_5738_;
v___y_5977_ = v___y_5739_;
v___y_5978_ = v___y_5740_;
goto v___jp_5967_;
}
else
{
lean_object* v_a_6190_; lean_object* v___x_6192_; uint8_t v_isShared_6193_; uint8_t v_isSharedCheck_6197_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6190_ = lean_ctor_get(v___x_6189_, 0);
v_isSharedCheck_6197_ = !lean_is_exclusive(v___x_6189_);
if (v_isSharedCheck_6197_ == 0)
{
v___x_6192_ = v___x_6189_;
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
else
{
lean_inc(v_a_6190_);
lean_dec(v___x_6189_);
v___x_6192_ = lean_box(0);
v_isShared_6193_ = v_isSharedCheck_6197_;
goto v_resetjp_6191_;
}
v_resetjp_6191_:
{
lean_object* v___x_6195_; 
if (v_isShared_6193_ == 0)
{
v___x_6195_ = v___x_6192_;
goto v_reusejp_6194_;
}
else
{
lean_object* v_reuseFailAlloc_6196_; 
v_reuseFailAlloc_6196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6196_, 0, v_a_6190_);
v___x_6195_ = v_reuseFailAlloc_6196_;
goto v_reusejp_6194_;
}
v_reusejp_6194_:
{
return v___x_6195_;
}
}
}
}
}
v___jp_5957_:
{
lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5961_; 
v___x_5958_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5958_, 0, v_a_5953_);
v___x_5959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5958_);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 0, v___x_5959_);
v___x_5961_ = v___x_5955_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v___x_5959_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
v___jp_5967_:
{
lean_object* v___x_5979_; 
lean_inc(v_goal_5728_);
v___x_5979_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_consumeMData_x3f___redArg(v_goal_5728_, v_a_5953_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5979_) == 0)
{
lean_object* v_a_5980_; 
v_a_5980_ = lean_ctor_get(v___x_5979_, 0);
lean_inc(v_a_5980_);
lean_dec_ref_known(v___x_5979_, 1);
if (lean_obj_tag(v_a_5980_) == 1)
{
lean_object* v_val_5981_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5981_ = lean_ctor_get(v_a_5980_, 0);
lean_inc(v_val_5981_);
lean_dec_ref_known(v_a_5980_, 1);
v_g_5747_ = v_val_5981_;
goto v___jp_5746_;
}
else
{
lean_object* v___x_5982_; 
lean_dec(v_a_5980_);
lean_inc(v_goal_5728_);
v___x_5982_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_5728_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5982_) == 0)
{
lean_object* v_a_5983_; 
v_a_5983_ = lean_ctor_get(v___x_5982_, 0);
lean_inc(v_a_5983_);
lean_dec_ref_known(v___x_5982_, 1);
if (lean_obj_tag(v_a_5983_) == 1)
{
lean_object* v_val_5984_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5984_ = lean_ctor_get(v_a_5983_, 0);
lean_inc(v_val_5984_);
lean_dec_ref_known(v_a_5983_, 1);
v_gs_5743_ = v_val_5984_;
goto v___jp_5742_;
}
else
{
lean_object* v___x_5985_; 
lean_dec(v_a_5983_);
lean_inc(v_a_5953_);
lean_inc(v_goal_5728_);
v___x_5985_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_5728_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5985_) == 0)
{
lean_object* v_a_5986_; 
v_a_5986_ = lean_ctor_get(v___x_5985_, 0);
lean_inc(v_a_5986_);
lean_dec_ref_known(v___x_5985_, 1);
if (lean_obj_tag(v_a_5986_) == 1)
{
lean_object* v_val_5987_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5987_ = lean_ctor_get(v_a_5986_, 0);
lean_inc(v_val_5987_);
lean_dec_ref_known(v_a_5986_, 1);
v_g_5747_ = v_val_5987_;
goto v___jp_5746_;
}
else
{
lean_object* v___x_5988_; 
lean_dec(v_a_5986_);
lean_inc(v_goal_5728_);
v___x_5988_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_5728_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5988_) == 0)
{
lean_object* v_a_5989_; 
v_a_5989_ = lean_ctor_get(v___x_5988_, 0);
lean_inc(v_a_5989_);
lean_dec_ref_known(v___x_5988_, 1);
if (lean_obj_tag(v_a_5989_) == 1)
{
lean_object* v_val_5990_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5990_ = lean_ctor_get(v_a_5989_, 0);
lean_inc(v_val_5990_);
lean_dec_ref_known(v_a_5989_, 1);
v_g_5747_ = v_val_5990_;
goto v___jp_5746_;
}
else
{
lean_object* v___x_5991_; 
lean_dec(v_a_5989_);
lean_inc(v_a_5953_);
lean_inc(v_goal_5728_);
v___x_5991_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_5728_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5991_) == 0)
{
lean_object* v_a_5992_; 
v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
lean_inc(v_a_5992_);
lean_dec_ref_known(v___x_5991_, 1);
if (lean_obj_tag(v_a_5992_) == 1)
{
lean_object* v_val_5993_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5993_ = lean_ctor_get(v_a_5992_, 0);
lean_inc(v_val_5993_);
lean_dec_ref_known(v_a_5992_, 1);
v_g_5747_ = v_val_5993_;
goto v___jp_5746_;
}
else
{
lean_object* v___x_5994_; 
lean_dec(v_a_5992_);
lean_inc(v_a_5953_);
lean_inc(v_goal_5728_);
lean_inc_ref(v_scope_5729_);
v___x_5994_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_5729_, v_goal_5728_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v_a_5995_; 
v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
lean_inc(v_a_5995_);
lean_dec_ref_known(v___x_5994_, 1);
if (lean_obj_tag(v_a_5995_) == 1)
{
lean_object* v_val_5996_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5996_ = lean_ctor_get(v_a_5995_, 0);
lean_inc(v_val_5996_);
lean_dec_ref_known(v_a_5995_, 1);
v_gs_5743_ = v_val_5996_;
goto v___jp_5742_;
}
else
{
lean_object* v___x_5997_; 
lean_dec(v_a_5995_);
lean_inc(v_a_5953_);
lean_inc(v_goal_5728_);
v___x_5997_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_instantiateGoal_x3f(v_goal_5728_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_5997_) == 0)
{
lean_object* v_a_5998_; 
v_a_5998_ = lean_ctor_get(v___x_5997_, 0);
lean_inc(v_a_5998_);
lean_dec_ref_known(v___x_5997_, 1);
if (lean_obj_tag(v_a_5998_) == 1)
{
lean_object* v_val_5999_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_5999_ = lean_ctor_get(v_a_5998_, 0);
lean_inc(v_val_5999_);
lean_dec_ref_known(v_a_5998_, 1);
v_g_5747_ = v_val_5999_;
goto v___jp_5746_;
}
else
{
lean_object* v___x_6000_; uint8_t v___x_6001_; 
lean_dec(v_a_5998_);
lean_inc(v_a_5953_);
v___x_6000_ = l_Lean_Expr_cleanupAnnotations(v_a_5953_);
v___x_6001_ = l_Lean_Expr_isApp(v___x_6000_);
if (v___x_6001_ == 0)
{
lean_dec_ref(v___x_6000_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
goto v___jp_5957_;
}
else
{
lean_object* v_arg_6002_; lean_object* v___x_6003_; uint8_t v___x_6004_; 
v_arg_6002_ = lean_ctor_get(v___x_6000_, 1);
lean_inc_ref(v_arg_6002_);
v___x_6003_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6000_);
v___x_6004_ = l_Lean_Expr_isApp(v___x_6003_);
if (v___x_6004_ == 0)
{
lean_dec_ref(v___x_6003_);
lean_dec_ref(v_arg_6002_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
goto v___jp_5957_;
}
else
{
lean_object* v_arg_6005_; lean_object* v___x_6006_; uint8_t v___x_6007_; 
v_arg_6005_ = lean_ctor_get(v___x_6003_, 1);
lean_inc_ref(v_arg_6005_);
v___x_6006_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6003_);
v___x_6007_ = l_Lean_Expr_isApp(v___x_6006_);
if (v___x_6007_ == 0)
{
lean_dec_ref(v___x_6006_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
goto v___jp_5957_;
}
else
{
lean_object* v_arg_6008_; lean_object* v___x_6009_; uint8_t v___x_6010_; 
v_arg_6008_ = lean_ctor_get(v___x_6006_, 1);
lean_inc_ref(v_arg_6008_);
v___x_6009_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6006_);
v___x_6010_ = l_Lean_Expr_isApp(v___x_6009_);
if (v___x_6010_ == 0)
{
lean_dec_ref(v___x_6009_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
goto v___jp_5957_;
}
else
{
lean_object* v_arg_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; uint8_t v___x_6014_; 
v_arg_6011_ = lean_ctor_get(v___x_6009_, 1);
lean_inc_ref(v_arg_6011_);
v___x_6012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6009_);
v___x_6013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_6014_ = l_Lean_Expr_isConstOf(v___x_6012_, v___x_6013_);
lean_dec_ref(v___x_6012_);
if (v___x_6014_ == 0)
{
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
goto v___jp_5957_;
}
else
{
lean_object* v___x_6015_; 
lean_del_object(v___x_5955_);
lean_inc(v_goal_5728_);
v___x_6015_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_5728_, v___y_5968_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6015_) == 0)
{
lean_object* v_a_6016_; 
v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
lean_inc(v_a_6016_);
lean_dec_ref_known(v___x_6015_, 1);
if (lean_obj_tag(v_a_6016_) == 1)
{
lean_object* v_val_6017_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_val_6017_ = lean_ctor_get(v_a_6016_, 0);
lean_inc(v_val_6017_);
lean_dec_ref_known(v_a_6016_, 1);
v_gs_5743_ = v_val_6017_;
goto v___jp_5742_;
}
else
{
lean_object* v___x_6018_; 
lean_dec(v_a_6016_);
lean_inc(v_a_5953_);
lean_inc_ref(v_arg_6005_);
lean_inc(v_goal_5728_);
lean_inc_ref(v_scope_5729_);
v___x_6018_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_5729_, v_goal_5728_, v_arg_6011_, v_arg_6005_, v_a_5953_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6018_) == 0)
{
lean_object* v_a_6019_; lean_object* v___x_6021_; uint8_t v_isShared_6022_; uint8_t v_isSharedCheck_6111_; 
v_a_6019_ = lean_ctor_get(v___x_6018_, 0);
v_isSharedCheck_6111_ = !lean_is_exclusive(v___x_6018_);
if (v_isSharedCheck_6111_ == 0)
{
v___x_6021_ = v___x_6018_;
v_isShared_6022_ = v_isSharedCheck_6111_;
goto v_resetjp_6020_;
}
else
{
lean_inc(v_a_6019_);
lean_dec(v___x_6018_);
v___x_6021_ = lean_box(0);
v_isShared_6022_ = v_isSharedCheck_6111_;
goto v_resetjp_6020_;
}
v_resetjp_6020_:
{
if (lean_obj_tag(v_a_6019_) == 1)
{
lean_object* v_val_6023_; lean_object* v_fst_6024_; lean_object* v_snd_6025_; lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6035_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_val_6023_ = lean_ctor_get(v_a_6019_, 0);
lean_inc(v_val_6023_);
lean_dec_ref_known(v_a_6019_, 1);
v_fst_6024_ = lean_ctor_get(v_val_6023_, 0);
v_snd_6025_ = lean_ctor_get(v_val_6023_, 1);
v_isSharedCheck_6035_ = !lean_is_exclusive(v_val_6023_);
if (v_isSharedCheck_6035_ == 0)
{
v___x_6027_ = v_val_6023_;
v_isShared_6028_ = v_isSharedCheck_6035_;
goto v_resetjp_6026_;
}
else
{
lean_inc(v_snd_6025_);
lean_inc(v_fst_6024_);
lean_dec(v_val_6023_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6035_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6030_; 
if (v_isShared_6028_ == 0)
{
v___x_6030_ = v___x_6027_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6034_; 
v_reuseFailAlloc_6034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6034_, 0, v_fst_6024_);
lean_ctor_set(v_reuseFailAlloc_6034_, 1, v_snd_6025_);
v___x_6030_ = v_reuseFailAlloc_6034_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
lean_object* v___x_6032_; 
if (v_isShared_6022_ == 0)
{
lean_ctor_set(v___x_6021_, 0, v___x_6030_);
v___x_6032_ = v___x_6021_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_6030_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
}
else
{
lean_object* v___x_6036_; 
lean_del_object(v___x_6021_);
lean_dec(v_a_6019_);
lean_inc(v_goal_5728_);
v___x_6036_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_5729_, v_goal_5728_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6036_) == 0)
{
lean_object* v_a_6037_; lean_object* v___x_6038_; 
v_a_6037_ = lean_ctor_get(v___x_6036_, 0);
lean_inc(v_a_6037_);
lean_dec_ref_known(v___x_6036_, 1);
lean_inc_ref(v_arg_6002_);
lean_inc_ref(v_arg_6005_);
lean_inc_ref(v_arg_6011_);
lean_inc(v_goal_5728_);
v___x_6038_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_5728_, v_a_5953_, v_arg_6011_, v_arg_6008_, v_arg_6005_, v_arg_6002_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
lean_inc(v_a_6039_);
lean_dec_ref_known(v___x_6038_, 1);
if (lean_obj_tag(v_a_6039_) == 1)
{
lean_object* v_val_6040_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_val_6040_ = lean_ctor_get(v_a_6039_, 0);
lean_inc(v_val_6040_);
lean_dec_ref_known(v_a_6039_, 1);
v___y_5759_ = v_a_6037_;
v_g_5760_ = v_val_6040_;
goto v___jp_5758_;
}
else
{
lean_object* v___x_6041_; 
lean_dec(v_a_6039_);
lean_inc_ref(v_arg_6002_);
lean_inc(v_goal_5728_);
v___x_6041_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_5728_, v_arg_6002_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6041_) == 0)
{
lean_object* v_a_6042_; 
v_a_6042_ = lean_ctor_get(v___x_6041_, 0);
lean_inc(v_a_6042_);
lean_dec_ref_known(v___x_6041_, 1);
if (lean_obj_tag(v_a_6042_) == 1)
{
lean_object* v_val_6043_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_val_6043_ = lean_ctor_get(v_a_6042_, 0);
lean_inc(v_val_6043_);
lean_dec_ref_known(v_a_6042_, 1);
v___y_5766_ = v_a_6037_;
v_gs_5767_ = v_val_6043_;
goto v___jp_5765_;
}
else
{
lean_object* v___x_6044_; 
lean_dec(v_a_6042_);
lean_inc(v_goal_5728_);
v___x_6044_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitForallLe_x3f(v_goal_5728_, v_arg_6002_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6044_) == 0)
{
lean_object* v_a_6045_; 
v_a_6045_ = lean_ctor_get(v___x_6044_, 0);
lean_inc(v_a_6045_);
lean_dec_ref_known(v___x_6044_, 1);
if (lean_obj_tag(v_a_6045_) == 1)
{
lean_object* v_val_6046_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_val_6046_ = lean_ctor_get(v_a_6045_, 0);
lean_inc(v_val_6046_);
lean_dec_ref_known(v_a_6045_, 1);
v___y_5766_ = v_a_6037_;
v_gs_5767_ = v_val_6046_;
goto v___jp_5765_;
}
else
{
lean_object* v___x_6047_; 
lean_dec(v_a_6045_);
lean_inc_ref(v_arg_6002_);
lean_inc_ref(v_arg_6005_);
lean_inc(v_goal_5728_);
lean_inc(v_a_6037_);
v___x_6047_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_a_6037_, v_goal_5728_, v_arg_6011_, v_arg_6005_, v_arg_6002_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
lean_dec_ref(v_arg_6011_);
if (lean_obj_tag(v___x_6047_) == 0)
{
lean_object* v_a_6048_; 
v_a_6048_ = lean_ctor_get(v___x_6047_, 0);
lean_inc(v_a_6048_);
lean_dec_ref_known(v___x_6047_, 1);
if (lean_obj_tag(v_a_6048_) == 1)
{
lean_object* v_val_6049_; 
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_val_6049_ = lean_ctor_get(v_a_6048_, 0);
lean_inc(v_val_6049_);
lean_dec_ref_known(v_a_6048_, 1);
v___y_5766_ = v_a_6037_;
v_gs_5767_ = v_val_6049_;
goto v___jp_5765_;
}
else
{
lean_object* v___x_6050_; 
lean_dec(v_a_6048_);
lean_inc_ref(v_arg_6002_);
v___x_6050_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(v_arg_6002_);
if (lean_obj_tag(v___x_6050_) == 1)
{
lean_object* v_options_6051_; uint8_t v_hasTrace_6052_; 
v_options_6051_ = lean_ctor_get(v___y_5977_, 2);
v_hasTrace_6052_ = lean_ctor_get_uint8(v_options_6051_, sizeof(void*)*1);
if (v_hasTrace_6052_ == 0)
{
lean_object* v_val_6053_; 
v_val_6053_ = lean_ctor_get(v___x_6050_, 0);
lean_inc(v_val_6053_);
lean_dec_ref_known(v___x_6050_, 1);
v___y_5819_ = v_arg_6002_;
v___y_5820_ = v_arg_6005_;
v___y_5821_ = v_a_6037_;
v___y_5822_ = v_val_6053_;
v___y_5823_ = v___y_5968_;
v___y_5824_ = v___y_5969_;
v___y_5825_ = v___y_5970_;
v___y_5826_ = v___y_5971_;
v___y_5827_ = v___y_5972_;
v___y_5828_ = v___y_5973_;
v___y_5829_ = v___y_5974_;
v___y_5830_ = v___y_5975_;
v___y_5831_ = v___y_5976_;
v___y_5832_ = v___y_5977_;
v___y_5833_ = v___y_5978_;
goto v___jp_5818_;
}
else
{
lean_object* v_val_6054_; lean_object* v_inheritedTraceOptions_6055_; lean_object* v___x_6056_; uint8_t v___x_6057_; 
v_val_6054_ = lean_ctor_get(v___x_6050_, 0);
lean_inc(v_val_6054_);
lean_dec_ref_known(v___x_6050_, 1);
v_inheritedTraceOptions_6055_ = lean_ctor_get(v___y_5977_, 13);
v___x_6056_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_6057_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6055_, v_options_6051_, v___x_6056_);
if (v___x_6057_ == 0)
{
v___y_5819_ = v_arg_6002_;
v___y_5820_ = v_arg_6005_;
v___y_5821_ = v_a_6037_;
v___y_5822_ = v_val_6054_;
v___y_5823_ = v___y_5968_;
v___y_5824_ = v___y_5969_;
v___y_5825_ = v___y_5970_;
v___y_5826_ = v___y_5971_;
v___y_5827_ = v___y_5972_;
v___y_5828_ = v___y_5973_;
v___y_5829_ = v___y_5974_;
v___y_5830_ = v___y_5975_;
v___y_5831_ = v___y_5976_;
v___y_5832_ = v___y_5977_;
v___y_5833_ = v___y_5978_;
goto v___jp_5818_;
}
else
{
lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6058_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5);
v___x_6059_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_val_6054_);
v___x_6060_ = l_Lean_MessageData_ofExpr(v___x_6059_);
v___x_6061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6058_);
lean_ctor_set(v___x_6061_, 1, v___x_6060_);
v___x_6062_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5966_, v___x_6061_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_);
if (lean_obj_tag(v___x_6062_) == 0)
{
lean_dec_ref_known(v___x_6062_, 1);
v___y_5819_ = v_arg_6002_;
v___y_5820_ = v_arg_6005_;
v___y_5821_ = v_a_6037_;
v___y_5822_ = v_val_6054_;
v___y_5823_ = v___y_5968_;
v___y_5824_ = v___y_5969_;
v___y_5825_ = v___y_5970_;
v___y_5826_ = v___y_5971_;
v___y_5827_ = v___y_5972_;
v___y_5828_ = v___y_5973_;
v___y_5829_ = v___y_5974_;
v___y_5830_ = v___y_5975_;
v___y_5831_ = v___y_5976_;
v___y_5832_ = v___y_5977_;
v___y_5833_ = v___y_5978_;
goto v___jp_5818_;
}
else
{
lean_object* v_a_6063_; lean_object* v___x_6065_; uint8_t v_isShared_6066_; uint8_t v_isSharedCheck_6070_; 
lean_dec(v_val_6054_);
lean_dec(v_a_6037_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_a_6063_ = lean_ctor_get(v___x_6062_, 0);
v_isSharedCheck_6070_ = !lean_is_exclusive(v___x_6062_);
if (v_isSharedCheck_6070_ == 0)
{
v___x_6065_ = v___x_6062_;
v_isShared_6066_ = v_isSharedCheck_6070_;
goto v_resetjp_6064_;
}
else
{
lean_inc(v_a_6063_);
lean_dec(v___x_6062_);
v___x_6065_ = lean_box(0);
v_isShared_6066_ = v_isSharedCheck_6070_;
goto v_resetjp_6064_;
}
v_resetjp_6064_:
{
lean_object* v___x_6068_; 
if (v_isShared_6066_ == 0)
{
v___x_6068_ = v___x_6065_;
goto v_reusejp_6067_;
}
else
{
lean_object* v_reuseFailAlloc_6069_; 
v_reuseFailAlloc_6069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6069_, 0, v_a_6063_);
v___x_6068_ = v_reuseFailAlloc_6069_;
goto v_reusejp_6067_;
}
v_reusejp_6067_:
{
return v___x_6068_;
}
}
}
}
}
}
else
{
lean_dec(v___x_6050_);
lean_dec(v_a_6037_);
lean_dec(v_goal_5728_);
v___y_5753_ = v_arg_6002_;
v___y_5754_ = v_arg_6005_;
goto v___jp_5752_;
}
}
}
else
{
lean_object* v_a_6071_; lean_object* v___x_6073_; uint8_t v_isShared_6074_; uint8_t v_isSharedCheck_6078_; 
lean_dec(v_a_6037_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_a_6071_ = lean_ctor_get(v___x_6047_, 0);
v_isSharedCheck_6078_ = !lean_is_exclusive(v___x_6047_);
if (v_isSharedCheck_6078_ == 0)
{
v___x_6073_ = v___x_6047_;
v_isShared_6074_ = v_isSharedCheck_6078_;
goto v_resetjp_6072_;
}
else
{
lean_inc(v_a_6071_);
lean_dec(v___x_6047_);
v___x_6073_ = lean_box(0);
v_isShared_6074_ = v_isSharedCheck_6078_;
goto v_resetjp_6072_;
}
v_resetjp_6072_:
{
lean_object* v___x_6076_; 
if (v_isShared_6074_ == 0)
{
v___x_6076_ = v___x_6073_;
goto v_reusejp_6075_;
}
else
{
lean_object* v_reuseFailAlloc_6077_; 
v_reuseFailAlloc_6077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6071_);
v___x_6076_ = v_reuseFailAlloc_6077_;
goto v_reusejp_6075_;
}
v_reusejp_6075_:
{
return v___x_6076_;
}
}
}
}
}
else
{
lean_object* v_a_6079_; lean_object* v___x_6081_; uint8_t v_isShared_6082_; uint8_t v_isSharedCheck_6086_; 
lean_dec(v_a_6037_);
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_a_6079_ = lean_ctor_get(v___x_6044_, 0);
v_isSharedCheck_6086_ = !lean_is_exclusive(v___x_6044_);
if (v_isSharedCheck_6086_ == 0)
{
v___x_6081_ = v___x_6044_;
v_isShared_6082_ = v_isSharedCheck_6086_;
goto v_resetjp_6080_;
}
else
{
lean_inc(v_a_6079_);
lean_dec(v___x_6044_);
v___x_6081_ = lean_box(0);
v_isShared_6082_ = v_isSharedCheck_6086_;
goto v_resetjp_6080_;
}
v_resetjp_6080_:
{
lean_object* v___x_6084_; 
if (v_isShared_6082_ == 0)
{
v___x_6084_ = v___x_6081_;
goto v_reusejp_6083_;
}
else
{
lean_object* v_reuseFailAlloc_6085_; 
v_reuseFailAlloc_6085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
v___x_6084_ = v_reuseFailAlloc_6085_;
goto v_reusejp_6083_;
}
v_reusejp_6083_:
{
return v___x_6084_;
}
}
}
}
}
else
{
lean_object* v_a_6087_; lean_object* v___x_6089_; uint8_t v_isShared_6090_; uint8_t v_isSharedCheck_6094_; 
lean_dec(v_a_6037_);
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_a_6087_ = lean_ctor_get(v___x_6041_, 0);
v_isSharedCheck_6094_ = !lean_is_exclusive(v___x_6041_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6089_ = v___x_6041_;
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
else
{
lean_inc(v_a_6087_);
lean_dec(v___x_6041_);
v___x_6089_ = lean_box(0);
v_isShared_6090_ = v_isSharedCheck_6094_;
goto v_resetjp_6088_;
}
v_resetjp_6088_:
{
lean_object* v___x_6092_; 
if (v_isShared_6090_ == 0)
{
v___x_6092_ = v___x_6089_;
goto v_reusejp_6091_;
}
else
{
lean_object* v_reuseFailAlloc_6093_; 
v_reuseFailAlloc_6093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6093_, 0, v_a_6087_);
v___x_6092_ = v_reuseFailAlloc_6093_;
goto v_reusejp_6091_;
}
v_reusejp_6091_:
{
return v___x_6092_;
}
}
}
}
}
else
{
lean_object* v_a_6095_; lean_object* v___x_6097_; uint8_t v_isShared_6098_; uint8_t v_isSharedCheck_6102_; 
lean_dec(v_a_6037_);
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_goal_5728_);
v_a_6095_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6102_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6102_ == 0)
{
v___x_6097_ = v___x_6038_;
v_isShared_6098_ = v_isSharedCheck_6102_;
goto v_resetjp_6096_;
}
else
{
lean_inc(v_a_6095_);
lean_dec(v___x_6038_);
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
}
else
{
lean_object* v_a_6103_; lean_object* v___x_6105_; uint8_t v_isShared_6106_; uint8_t v_isSharedCheck_6110_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_a_5953_);
lean_dec(v_goal_5728_);
v_a_6103_ = lean_ctor_get(v___x_6036_, 0);
v_isSharedCheck_6110_ = !lean_is_exclusive(v___x_6036_);
if (v_isSharedCheck_6110_ == 0)
{
v___x_6105_ = v___x_6036_;
v_isShared_6106_ = v_isSharedCheck_6110_;
goto v_resetjp_6104_;
}
else
{
lean_inc(v_a_6103_);
lean_dec(v___x_6036_);
v___x_6105_ = lean_box(0);
v_isShared_6106_ = v_isSharedCheck_6110_;
goto v_resetjp_6104_;
}
v_resetjp_6104_:
{
lean_object* v___x_6108_; 
if (v_isShared_6106_ == 0)
{
v___x_6108_ = v___x_6105_;
goto v_reusejp_6107_;
}
else
{
lean_object* v_reuseFailAlloc_6109_; 
v_reuseFailAlloc_6109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6109_, 0, v_a_6103_);
v___x_6108_ = v_reuseFailAlloc_6109_;
goto v_reusejp_6107_;
}
v_reusejp_6107_:
{
return v___x_6108_;
}
}
}
}
}
}
else
{
lean_object* v_a_6112_; lean_object* v___x_6114_; uint8_t v_isShared_6115_; uint8_t v_isSharedCheck_6119_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6112_ = lean_ctor_get(v___x_6018_, 0);
v_isSharedCheck_6119_ = !lean_is_exclusive(v___x_6018_);
if (v_isSharedCheck_6119_ == 0)
{
v___x_6114_ = v___x_6018_;
v_isShared_6115_ = v_isSharedCheck_6119_;
goto v_resetjp_6113_;
}
else
{
lean_inc(v_a_6112_);
lean_dec(v___x_6018_);
v___x_6114_ = lean_box(0);
v_isShared_6115_ = v_isSharedCheck_6119_;
goto v_resetjp_6113_;
}
v_resetjp_6113_:
{
lean_object* v___x_6117_; 
if (v_isShared_6115_ == 0)
{
v___x_6117_ = v___x_6114_;
goto v_reusejp_6116_;
}
else
{
lean_object* v_reuseFailAlloc_6118_; 
v_reuseFailAlloc_6118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6118_, 0, v_a_6112_);
v___x_6117_ = v_reuseFailAlloc_6118_;
goto v_reusejp_6116_;
}
v_reusejp_6116_:
{
return v___x_6117_;
}
}
}
}
}
else
{
lean_object* v_a_6120_; lean_object* v___x_6122_; uint8_t v_isShared_6123_; uint8_t v_isSharedCheck_6127_; 
lean_dec_ref(v_arg_6011_);
lean_dec_ref(v_arg_6008_);
lean_dec_ref(v_arg_6005_);
lean_dec_ref(v_arg_6002_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6120_ = lean_ctor_get(v___x_6015_, 0);
v_isSharedCheck_6127_ = !lean_is_exclusive(v___x_6015_);
if (v_isSharedCheck_6127_ == 0)
{
v___x_6122_ = v___x_6015_;
v_isShared_6123_ = v_isSharedCheck_6127_;
goto v_resetjp_6121_;
}
else
{
lean_inc(v_a_6120_);
lean_dec(v___x_6015_);
v___x_6122_ = lean_box(0);
v_isShared_6123_ = v_isSharedCheck_6127_;
goto v_resetjp_6121_;
}
v_resetjp_6121_:
{
lean_object* v___x_6125_; 
if (v_isShared_6123_ == 0)
{
v___x_6125_ = v___x_6122_;
goto v_reusejp_6124_;
}
else
{
lean_object* v_reuseFailAlloc_6126_; 
v_reuseFailAlloc_6126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6126_, 0, v_a_6120_);
v___x_6125_ = v_reuseFailAlloc_6126_;
goto v_reusejp_6124_;
}
v_reusejp_6124_:
{
return v___x_6125_;
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
lean_object* v_a_6128_; lean_object* v___x_6130_; uint8_t v_isShared_6131_; uint8_t v_isSharedCheck_6135_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6128_ = lean_ctor_get(v___x_5997_, 0);
v_isSharedCheck_6135_ = !lean_is_exclusive(v___x_5997_);
if (v_isSharedCheck_6135_ == 0)
{
v___x_6130_ = v___x_5997_;
v_isShared_6131_ = v_isSharedCheck_6135_;
goto v_resetjp_6129_;
}
else
{
lean_inc(v_a_6128_);
lean_dec(v___x_5997_);
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
}
else
{
lean_object* v_a_6136_; lean_object* v___x_6138_; uint8_t v_isShared_6139_; uint8_t v_isSharedCheck_6143_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6136_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6143_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6143_ == 0)
{
v___x_6138_ = v___x_5994_;
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
else
{
lean_inc(v_a_6136_);
lean_dec(v___x_5994_);
v___x_6138_ = lean_box(0);
v_isShared_6139_ = v_isSharedCheck_6143_;
goto v_resetjp_6137_;
}
v_resetjp_6137_:
{
lean_object* v___x_6141_; 
if (v_isShared_6139_ == 0)
{
v___x_6141_ = v___x_6138_;
goto v_reusejp_6140_;
}
else
{
lean_object* v_reuseFailAlloc_6142_; 
v_reuseFailAlloc_6142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6142_, 0, v_a_6136_);
v___x_6141_ = v_reuseFailAlloc_6142_;
goto v_reusejp_6140_;
}
v_reusejp_6140_:
{
return v___x_6141_;
}
}
}
}
}
else
{
lean_object* v_a_6144_; lean_object* v___x_6146_; uint8_t v_isShared_6147_; uint8_t v_isSharedCheck_6151_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6144_ = lean_ctor_get(v___x_5991_, 0);
v_isSharedCheck_6151_ = !lean_is_exclusive(v___x_5991_);
if (v_isSharedCheck_6151_ == 0)
{
v___x_6146_ = v___x_5991_;
v_isShared_6147_ = v_isSharedCheck_6151_;
goto v_resetjp_6145_;
}
else
{
lean_inc(v_a_6144_);
lean_dec(v___x_5991_);
v___x_6146_ = lean_box(0);
v_isShared_6147_ = v_isSharedCheck_6151_;
goto v_resetjp_6145_;
}
v_resetjp_6145_:
{
lean_object* v___x_6149_; 
if (v_isShared_6147_ == 0)
{
v___x_6149_ = v___x_6146_;
goto v_reusejp_6148_;
}
else
{
lean_object* v_reuseFailAlloc_6150_; 
v_reuseFailAlloc_6150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6150_, 0, v_a_6144_);
v___x_6149_ = v_reuseFailAlloc_6150_;
goto v_reusejp_6148_;
}
v_reusejp_6148_:
{
return v___x_6149_;
}
}
}
}
}
else
{
lean_object* v_a_6152_; lean_object* v___x_6154_; uint8_t v_isShared_6155_; uint8_t v_isSharedCheck_6159_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6152_ = lean_ctor_get(v___x_5988_, 0);
v_isSharedCheck_6159_ = !lean_is_exclusive(v___x_5988_);
if (v_isSharedCheck_6159_ == 0)
{
v___x_6154_ = v___x_5988_;
v_isShared_6155_ = v_isSharedCheck_6159_;
goto v_resetjp_6153_;
}
else
{
lean_inc(v_a_6152_);
lean_dec(v___x_5988_);
v___x_6154_ = lean_box(0);
v_isShared_6155_ = v_isSharedCheck_6159_;
goto v_resetjp_6153_;
}
v_resetjp_6153_:
{
lean_object* v___x_6157_; 
if (v_isShared_6155_ == 0)
{
v___x_6157_ = v___x_6154_;
goto v_reusejp_6156_;
}
else
{
lean_object* v_reuseFailAlloc_6158_; 
v_reuseFailAlloc_6158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6158_, 0, v_a_6152_);
v___x_6157_ = v_reuseFailAlloc_6158_;
goto v_reusejp_6156_;
}
v_reusejp_6156_:
{
return v___x_6157_;
}
}
}
}
}
else
{
lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6160_ = lean_ctor_get(v___x_5985_, 0);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_5985_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6162_ = v___x_5985_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_dec(v___x_5985_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6165_; 
if (v_isShared_6163_ == 0)
{
v___x_6165_ = v___x_6162_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
else
{
lean_object* v_a_6168_; lean_object* v___x_6170_; uint8_t v_isShared_6171_; uint8_t v_isSharedCheck_6175_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6168_ = lean_ctor_get(v___x_5982_, 0);
v_isSharedCheck_6175_ = !lean_is_exclusive(v___x_5982_);
if (v_isSharedCheck_6175_ == 0)
{
v___x_6170_ = v___x_5982_;
v_isShared_6171_ = v_isSharedCheck_6175_;
goto v_resetjp_6169_;
}
else
{
lean_inc(v_a_6168_);
lean_dec(v___x_5982_);
v___x_6170_ = lean_box(0);
v_isShared_6171_ = v_isSharedCheck_6175_;
goto v_resetjp_6169_;
}
v_resetjp_6169_:
{
lean_object* v___x_6173_; 
if (v_isShared_6171_ == 0)
{
v___x_6173_ = v___x_6170_;
goto v_reusejp_6172_;
}
else
{
lean_object* v_reuseFailAlloc_6174_; 
v_reuseFailAlloc_6174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_a_6168_);
v___x_6173_ = v_reuseFailAlloc_6174_;
goto v_reusejp_6172_;
}
v_reusejp_6172_:
{
return v___x_6173_;
}
}
}
}
}
else
{
lean_object* v_a_6176_; lean_object* v___x_6178_; uint8_t v_isShared_6179_; uint8_t v_isSharedCheck_6183_; 
lean_del_object(v___x_5955_);
lean_dec(v_a_5953_);
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6176_ = lean_ctor_get(v___x_5979_, 0);
v_isSharedCheck_6183_ = !lean_is_exclusive(v___x_5979_);
if (v_isSharedCheck_6183_ == 0)
{
v___x_6178_ = v___x_5979_;
v_isShared_6179_ = v_isSharedCheck_6183_;
goto v_resetjp_6177_;
}
else
{
lean_inc(v_a_6176_);
lean_dec(v___x_5979_);
v___x_6178_ = lean_box(0);
v_isShared_6179_ = v_isSharedCheck_6183_;
goto v_resetjp_6177_;
}
v_resetjp_6177_:
{
lean_object* v___x_6181_; 
if (v_isShared_6179_ == 0)
{
v___x_6181_ = v___x_6178_;
goto v_reusejp_6180_;
}
else
{
lean_object* v_reuseFailAlloc_6182_; 
v_reuseFailAlloc_6182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6182_, 0, v_a_6176_);
v___x_6181_ = v_reuseFailAlloc_6182_;
goto v_reusejp_6180_;
}
v_reusejp_6180_:
{
return v___x_6181_;
}
}
}
}
}
}
else
{
lean_object* v_a_6199_; lean_object* v___x_6201_; uint8_t v_isShared_6202_; uint8_t v_isSharedCheck_6206_; 
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6199_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_6206_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_6206_ == 0)
{
v___x_6201_ = v___x_5952_;
v_isShared_6202_ = v_isSharedCheck_6206_;
goto v_resetjp_6200_;
}
else
{
lean_inc(v_a_6199_);
lean_dec(v___x_5952_);
v___x_6201_ = lean_box(0);
v_isShared_6202_ = v_isSharedCheck_6206_;
goto v_resetjp_6200_;
}
v_resetjp_6200_:
{
lean_object* v___x_6204_; 
if (v_isShared_6202_ == 0)
{
v___x_6204_ = v___x_6201_;
goto v_reusejp_6203_;
}
else
{
lean_object* v_reuseFailAlloc_6205_; 
v_reuseFailAlloc_6205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6205_, 0, v_a_6199_);
v___x_6204_ = v_reuseFailAlloc_6205_;
goto v_reusejp_6203_;
}
v_reusejp_6203_:
{
return v___x_6204_;
}
}
}
}
else
{
lean_object* v___x_6207_; lean_object* v___x_6209_; 
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v___x_6207_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
if (v_isShared_5950_ == 0)
{
lean_ctor_set(v___x_5949_, 0, v___x_6207_);
v___x_6209_ = v___x_5949_;
goto v_reusejp_6208_;
}
else
{
lean_object* v_reuseFailAlloc_6210_; 
v_reuseFailAlloc_6210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6210_, 0, v___x_6207_);
v___x_6209_ = v_reuseFailAlloc_6210_;
goto v_reusejp_6208_;
}
v_reusejp_6208_:
{
return v___x_6209_;
}
}
}
}
else
{
lean_object* v_a_6212_; lean_object* v___x_6214_; uint8_t v_isShared_6215_; uint8_t v_isSharedCheck_6219_; 
lean_dec_ref(v_scope_5729_);
lean_dec(v_goal_5728_);
v_a_6212_ = lean_ctor_get(v___x_5946_, 0);
v_isSharedCheck_6219_ = !lean_is_exclusive(v___x_5946_);
if (v_isSharedCheck_6219_ == 0)
{
v___x_6214_ = v___x_5946_;
v_isShared_6215_ = v_isSharedCheck_6219_;
goto v_resetjp_6213_;
}
else
{
lean_inc(v_a_6212_);
lean_dec(v___x_5946_);
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
v___jp_5742_:
{
lean_object* v___x_5744_; lean_object* v___x_5745_; 
v___x_5744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5744_, 0, v_scope_5729_);
lean_ctor_set(v___x_5744_, 1, v_gs_5743_);
v___x_5745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5744_);
return v___x_5745_;
}
v___jp_5746_:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5751_; 
v___x_5748_ = lean_box(0);
v___x_5749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5749_, 0, v_g_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5750_, 0, v_scope_5729_);
lean_ctor_set(v___x_5750_, 1, v___x_5749_);
v___x_5751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5751_, 0, v___x_5750_);
return v___x_5751_;
}
v___jp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; 
v___x_5755_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5755_, 0, v___y_5754_);
lean_ctor_set(v___x_5755_, 1, v___y_5753_);
v___x_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
v___x_5757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5757_, 0, v___x_5756_);
return v___x_5757_;
}
v___jp_5758_:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5761_ = lean_box(0);
v___x_5762_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5762_, 0, v_g_5760_);
lean_ctor_set(v___x_5762_, 1, v___x_5761_);
v___x_5763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5763_, 0, v___y_5759_);
lean_ctor_set(v___x_5763_, 1, v___x_5762_);
v___x_5764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5764_, 0, v___x_5763_);
return v___x_5764_;
}
v___jp_5765_:
{
lean_object* v___x_5768_; lean_object* v___x_5769_; 
v___x_5768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5768_, 0, v___y_5766_);
lean_ctor_set(v___x_5768_, 1, v_gs_5767_);
v___x_5769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5769_, 0, v___x_5768_);
return v___x_5769_;
}
v___jp_5770_:
{
lean_object* v___x_5774_; 
v___x_5774_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5773_);
if (lean_obj_tag(v___x_5774_) == 0)
{
lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5784_; 
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5774_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; 
v_unused_5785_ = lean_ctor_get(v___x_5774_, 0);
lean_dec(v_unused_5785_);
v___x_5776_ = v___x_5774_;
v_isShared_5777_ = v_isSharedCheck_5784_;
goto v_resetjp_5775_;
}
else
{
lean_dec(v___x_5774_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5784_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v___x_5778_; lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5782_; 
v___x_5778_ = lean_box(0);
v___x_5779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5779_, 0, v_g_5772_);
lean_ctor_set(v___x_5779_, 1, v___x_5778_);
v___x_5780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5780_, 0, v___y_5771_);
lean_ctor_set(v___x_5780_, 1, v___x_5779_);
if (v_isShared_5777_ == 0)
{
lean_ctor_set(v___x_5776_, 0, v___x_5780_);
v___x_5782_ = v___x_5776_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5780_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
lean_dec(v_g_5772_);
lean_dec_ref(v___y_5771_);
v_a_5786_ = lean_ctor_get(v___x_5774_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v___x_5774_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5788_ = v___x_5774_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5774_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
v___jp_5794_:
{
lean_object* v___x_5808_; 
v___x_5808_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5804_);
if (lean_obj_tag(v___x_5808_) == 0)
{
lean_object* v___x_5809_; 
lean_dec_ref_known(v___x_5808_, 1);
v___x_5809_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v___y_5801_, v_goal_5728_, v___y_5797_, v___y_5806_, v___y_5804_, v___y_5798_, v___y_5795_, v___y_5807_, v___y_5805_, v___y_5802_, v___y_5803_, v___y_5800_, v___y_5796_, v___y_5799_);
return v___x_5809_;
}
else
{
lean_object* v_a_5810_; lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5817_; 
lean_dec_ref(v___y_5801_);
lean_dec_ref(v___y_5797_);
lean_dec(v_goal_5728_);
v_a_5810_ = lean_ctor_get(v___x_5808_, 0);
v_isSharedCheck_5817_ = !lean_is_exclusive(v___x_5808_);
if (v_isSharedCheck_5817_ == 0)
{
v___x_5812_ = v___x_5808_;
v_isShared_5813_ = v_isSharedCheck_5817_;
goto v_resetjp_5811_;
}
else
{
lean_inc(v_a_5810_);
lean_dec(v___x_5808_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5817_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v___x_5815_; 
if (v_isShared_5813_ == 0)
{
v___x_5815_ = v___x_5812_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5816_; 
v_reuseFailAlloc_5816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5816_, 0, v_a_5810_);
v___x_5815_ = v_reuseFailAlloc_5816_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
return v___x_5815_;
}
}
}
}
v___jp_5818_:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; 
lean_dec_ref(v___y_5820_);
lean_dec_ref(v___y_5819_);
v___x_5834_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v___y_5822_);
lean_inc_ref(v___x_5834_);
v___x_5835_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v___x_5834_, v___y_5823_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5835_) == 0)
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5937_; 
v_a_5836_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5937_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5937_ == 0)
{
v___x_5838_ = v___x_5835_;
v_isShared_5839_ = v_isSharedCheck_5937_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5835_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5937_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
uint8_t v___x_5840_; 
v___x_5840_ = lean_unbox(v_a_5836_);
lean_dec(v_a_5836_);
if (v___x_5840_ == 0)
{
lean_object* v___x_5841_; 
lean_del_object(v___x_5838_);
lean_inc_ref(v___y_5822_);
lean_inc(v_goal_5728_);
v___x_5841_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_5728_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5841_) == 0)
{
lean_object* v_a_5842_; 
v_a_5842_ = lean_ctor_get(v___x_5841_, 0);
lean_inc(v_a_5842_);
lean_dec_ref_known(v___x_5841_, 1);
if (lean_obj_tag(v_a_5842_) == 1)
{
lean_object* v_val_5843_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec(v_goal_5728_);
v_val_5843_ = lean_ctor_get(v_a_5842_, 0);
lean_inc(v_val_5843_);
lean_dec_ref_known(v_a_5842_, 1);
v___y_5759_ = v___y_5821_;
v_g_5760_ = v_val_5843_;
goto v___jp_5758_;
}
else
{
lean_object* v___x_5844_; 
lean_dec(v_a_5842_);
lean_inc_ref(v___y_5822_);
lean_inc(v_goal_5728_);
v___x_5844_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_5728_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5844_) == 0)
{
lean_object* v_a_5845_; 
v_a_5845_ = lean_ctor_get(v___x_5844_, 0);
lean_inc(v_a_5845_);
lean_dec_ref_known(v___x_5844_, 1);
if (lean_obj_tag(v_a_5845_) == 1)
{
lean_object* v_val_5846_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec(v_goal_5728_);
v_val_5846_ = lean_ctor_get(v_a_5845_, 0);
lean_inc(v_val_5846_);
lean_dec_ref_known(v_a_5845_, 1);
v___y_5771_ = v___y_5821_;
v_g_5772_ = v_val_5846_;
v___y_5773_ = v___y_5824_;
goto v___jp_5770_;
}
else
{
lean_object* v___x_5847_; 
lean_dec(v_a_5845_);
lean_inc_ref(v___y_5822_);
lean_inc(v_goal_5728_);
v___x_5847_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_5728_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5847_) == 0)
{
lean_object* v_a_5848_; 
v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
lean_inc(v_a_5848_);
lean_dec_ref_known(v___x_5847_, 1);
if (lean_obj_tag(v_a_5848_) == 1)
{
lean_object* v_val_5849_; lean_object* v___x_5850_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec(v_goal_5728_);
v_val_5849_ = lean_ctor_get(v_a_5848_, 0);
lean_inc(v_val_5849_);
lean_dec_ref_known(v_a_5848_, 1);
v___x_5850_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5824_);
if (lean_obj_tag(v___x_5850_) == 0)
{
lean_object* v___x_5852_; uint8_t v_isShared_5853_; uint8_t v_isSharedCheck_5858_; 
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5850_);
if (v_isSharedCheck_5858_ == 0)
{
lean_object* v_unused_5859_; 
v_unused_5859_ = lean_ctor_get(v___x_5850_, 0);
lean_dec(v_unused_5859_);
v___x_5852_ = v___x_5850_;
v_isShared_5853_ = v_isSharedCheck_5858_;
goto v_resetjp_5851_;
}
else
{
lean_dec(v___x_5850_);
v___x_5852_ = lean_box(0);
v_isShared_5853_ = v_isSharedCheck_5858_;
goto v_resetjp_5851_;
}
v_resetjp_5851_:
{
lean_object* v___x_5854_; lean_object* v___x_5856_; 
v___x_5854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5854_, 0, v___y_5821_);
lean_ctor_set(v___x_5854_, 1, v_val_5849_);
if (v_isShared_5853_ == 0)
{
lean_ctor_set(v___x_5852_, 0, v___x_5854_);
v___x_5856_ = v___x_5852_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v___x_5854_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
else
{
lean_object* v_a_5860_; lean_object* v___x_5862_; uint8_t v_isShared_5863_; uint8_t v_isSharedCheck_5867_; 
lean_dec(v_val_5849_);
lean_dec_ref(v___y_5821_);
v_a_5860_ = lean_ctor_get(v___x_5850_, 0);
v_isSharedCheck_5867_ = !lean_is_exclusive(v___x_5850_);
if (v_isSharedCheck_5867_ == 0)
{
v___x_5862_ = v___x_5850_;
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
else
{
lean_inc(v_a_5860_);
lean_dec(v___x_5850_);
v___x_5862_ = lean_box(0);
v_isShared_5863_ = v_isSharedCheck_5867_;
goto v_resetjp_5861_;
}
v_resetjp_5861_:
{
lean_object* v___x_5865_; 
if (v_isShared_5863_ == 0)
{
v___x_5865_ = v___x_5862_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5866_; 
v_reuseFailAlloc_5866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5866_, 0, v_a_5860_);
v___x_5865_ = v_reuseFailAlloc_5866_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
return v___x_5865_;
}
}
}
}
else
{
lean_object* v___x_5868_; 
lean_dec(v_a_5848_);
lean_inc_ref(v___y_5822_);
lean_inc(v_goal_5728_);
v___x_5868_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_5728_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5868_) == 0)
{
lean_object* v_a_5869_; 
v_a_5869_ = lean_ctor_get(v___x_5868_, 0);
lean_inc(v_a_5869_);
lean_dec_ref_known(v___x_5868_, 1);
if (lean_obj_tag(v_a_5869_) == 1)
{
lean_object* v_val_5870_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec(v_goal_5728_);
v_val_5870_ = lean_ctor_get(v_a_5869_, 0);
lean_inc(v_val_5870_);
lean_dec_ref_known(v_a_5869_, 1);
v___y_5771_ = v___y_5821_;
v_g_5772_ = v_val_5870_;
v___y_5773_ = v___y_5824_;
goto v___jp_5770_;
}
else
{
lean_object* v___x_5871_; 
lean_dec(v_a_5869_);
lean_inc_ref(v___y_5822_);
lean_inc(v_goal_5728_);
v___x_5871_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_5728_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
if (lean_obj_tag(v___x_5871_) == 0)
{
lean_object* v_a_5872_; 
v_a_5872_ = lean_ctor_get(v___x_5871_, 0);
lean_inc(v_a_5872_);
lean_dec_ref_known(v___x_5871_, 1);
if (lean_obj_tag(v_a_5872_) == 1)
{
lean_object* v_val_5873_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec(v_goal_5728_);
v_val_5873_ = lean_ctor_get(v_a_5872_, 0);
lean_inc(v_val_5873_);
lean_dec_ref_known(v_a_5872_, 1);
v___y_5771_ = v___y_5821_;
v_g_5772_ = v_val_5873_;
v___y_5773_ = v___y_5824_;
goto v___jp_5770_;
}
else
{
lean_object* v___x_5874_; uint8_t v___x_5875_; 
lean_dec(v_a_5872_);
v___x_5874_ = l_Lean_Expr_getAppFn(v___x_5834_);
v___x_5875_ = l_Lean_Expr_isConst(v___x_5874_);
if (v___x_5875_ == 0)
{
uint8_t v___x_5876_; 
v___x_5876_ = l_Lean_Expr_isFVar(v___x_5874_);
lean_dec_ref(v___x_5874_);
if (v___x_5876_ == 0)
{
lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v___x_5877_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v___x_5878_ = l_Lean_MessageData_ofExpr(v___x_5834_);
v___x_5879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5879_, 0, v___x_5877_);
lean_ctor_set(v___x_5879_, 1, v___x_5878_);
v___x_5880_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3);
v___x_5881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5881_, 0, v___x_5879_);
lean_ctor_set(v___x_5881_, 1, v___x_5880_);
v___x_5882_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5881_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_);
v_a_5883_ = lean_ctor_get(v___x_5882_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5882_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5882_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5882_);
v___x_5885_ = lean_box(0);
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
v_resetjp_5884_:
{
lean_object* v___x_5888_; 
if (v_isShared_5886_ == 0)
{
v___x_5888_ = v___x_5885_;
goto v_reusejp_5887_;
}
else
{
lean_object* v_reuseFailAlloc_5889_; 
v_reuseFailAlloc_5889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5889_, 0, v_a_5883_);
v___x_5888_ = v_reuseFailAlloc_5889_;
goto v_reusejp_5887_;
}
v_reusejp_5887_:
{
return v___x_5888_;
}
}
}
else
{
lean_dec_ref(v___x_5834_);
v___y_5795_ = v___y_5826_;
v___y_5796_ = v___y_5832_;
v___y_5797_ = v___y_5822_;
v___y_5798_ = v___y_5825_;
v___y_5799_ = v___y_5833_;
v___y_5800_ = v___y_5831_;
v___y_5801_ = v___y_5821_;
v___y_5802_ = v___y_5829_;
v___y_5803_ = v___y_5830_;
v___y_5804_ = v___y_5824_;
v___y_5805_ = v___y_5828_;
v___y_5806_ = v___y_5823_;
v___y_5807_ = v___y_5827_;
goto v___jp_5794_;
}
}
else
{
lean_dec_ref(v___x_5874_);
lean_dec_ref(v___x_5834_);
v___y_5795_ = v___y_5826_;
v___y_5796_ = v___y_5832_;
v___y_5797_ = v___y_5822_;
v___y_5798_ = v___y_5825_;
v___y_5799_ = v___y_5833_;
v___y_5800_ = v___y_5831_;
v___y_5801_ = v___y_5821_;
v___y_5802_ = v___y_5829_;
v___y_5803_ = v___y_5830_;
v___y_5804_ = v___y_5824_;
v___y_5805_ = v___y_5828_;
v___y_5806_ = v___y_5823_;
v___y_5807_ = v___y_5827_;
goto v___jp_5794_;
}
}
}
else
{
lean_object* v_a_5891_; lean_object* v___x_5893_; uint8_t v_isShared_5894_; uint8_t v_isSharedCheck_5898_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v_a_5891_ = lean_ctor_get(v___x_5871_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5871_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5871_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5871_);
v___x_5893_ = lean_box(0);
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
v_resetjp_5892_:
{
lean_object* v___x_5896_; 
if (v_isShared_5894_ == 0)
{
v___x_5896_ = v___x_5893_;
goto v_reusejp_5895_;
}
else
{
lean_object* v_reuseFailAlloc_5897_; 
v_reuseFailAlloc_5897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_a_5891_);
v___x_5896_ = v_reuseFailAlloc_5897_;
goto v_reusejp_5895_;
}
v_reusejp_5895_:
{
return v___x_5896_;
}
}
}
}
}
else
{
lean_object* v_a_5899_; lean_object* v___x_5901_; uint8_t v_isShared_5902_; uint8_t v_isSharedCheck_5906_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v_a_5899_ = lean_ctor_get(v___x_5868_, 0);
v_isSharedCheck_5906_ = !lean_is_exclusive(v___x_5868_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5901_ = v___x_5868_;
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
else
{
lean_inc(v_a_5899_);
lean_dec(v___x_5868_);
v___x_5901_ = lean_box(0);
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
v_resetjp_5900_:
{
lean_object* v___x_5904_; 
if (v_isShared_5902_ == 0)
{
v___x_5904_ = v___x_5901_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
v___x_5904_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
return v___x_5904_;
}
}
}
}
}
else
{
lean_object* v_a_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5914_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v_a_5907_ = lean_ctor_get(v___x_5847_, 0);
v_isSharedCheck_5914_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5914_ == 0)
{
v___x_5909_ = v___x_5847_;
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_a_5907_);
lean_dec(v___x_5847_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
lean_object* v___x_5912_; 
if (v_isShared_5910_ == 0)
{
v___x_5912_ = v___x_5909_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5907_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
}
}
}
else
{
lean_object* v_a_5915_; lean_object* v___x_5917_; uint8_t v_isShared_5918_; uint8_t v_isSharedCheck_5922_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v_a_5915_ = lean_ctor_get(v___x_5844_, 0);
v_isSharedCheck_5922_ = !lean_is_exclusive(v___x_5844_);
if (v_isSharedCheck_5922_ == 0)
{
v___x_5917_ = v___x_5844_;
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_a_5915_);
lean_dec(v___x_5844_);
v___x_5917_ = lean_box(0);
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
v_resetjp_5916_:
{
lean_object* v___x_5920_; 
if (v_isShared_5918_ == 0)
{
v___x_5920_ = v___x_5917_;
goto v_reusejp_5919_;
}
else
{
lean_object* v_reuseFailAlloc_5921_; 
v_reuseFailAlloc_5921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5921_, 0, v_a_5915_);
v___x_5920_ = v_reuseFailAlloc_5921_;
goto v_reusejp_5919_;
}
v_reusejp_5919_:
{
return v___x_5920_;
}
}
}
}
}
else
{
lean_object* v_a_5923_; lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5930_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v_a_5923_ = lean_ctor_get(v___x_5841_, 0);
v_isSharedCheck_5930_ = !lean_is_exclusive(v___x_5841_);
if (v_isSharedCheck_5930_ == 0)
{
v___x_5925_ = v___x_5841_;
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_a_5923_);
lean_dec(v___x_5841_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v___x_5928_; 
if (v_isShared_5926_ == 0)
{
v___x_5928_ = v___x_5925_;
goto v_reusejp_5927_;
}
else
{
lean_object* v_reuseFailAlloc_5929_; 
v_reuseFailAlloc_5929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5929_, 0, v_a_5923_);
v___x_5928_ = v_reuseFailAlloc_5929_;
goto v_reusejp_5927_;
}
v_reusejp_5927_:
{
return v___x_5928_;
}
}
}
}
else
{
lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5935_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v___x_5931_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v___y_5822_);
lean_dec_ref(v___y_5822_);
v___x_5932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5931_);
v___x_5933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5933_, 0, v___x_5932_);
if (v_isShared_5839_ == 0)
{
lean_ctor_set(v___x_5838_, 0, v___x_5933_);
v___x_5935_ = v___x_5838_;
goto v_reusejp_5934_;
}
else
{
lean_object* v_reuseFailAlloc_5936_; 
v_reuseFailAlloc_5936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5936_, 0, v___x_5933_);
v___x_5935_ = v_reuseFailAlloc_5936_;
goto v_reusejp_5934_;
}
v_reusejp_5934_:
{
return v___x_5935_;
}
}
}
}
else
{
lean_object* v_a_5938_; lean_object* v___x_5940_; uint8_t v_isShared_5941_; uint8_t v_isSharedCheck_5945_; 
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v_goal_5728_);
v_a_5938_ = lean_ctor_get(v___x_5835_, 0);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5835_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5940_ = v___x_5835_;
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
else
{
lean_inc(v_a_5938_);
lean_dec(v___x_5835_);
v___x_5940_ = lean_box(0);
v_isShared_5941_ = v_isSharedCheck_5945_;
goto v_resetjp_5939_;
}
v_resetjp_5939_:
{
lean_object* v___x_5943_; 
if (v_isShared_5941_ == 0)
{
v___x_5943_ = v___x_5940_;
goto v_reusejp_5942_;
}
else
{
lean_object* v_reuseFailAlloc_5944_; 
v_reuseFailAlloc_5944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5944_, 0, v_a_5938_);
v___x_5943_ = v_reuseFailAlloc_5944_;
goto v_reusejp_5942_;
}
v_reusejp_5942_:
{
return v___x_5943_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_6220_, lean_object* v_scope_6221_, lean_object* v___y_6222_, lean_object* v___y_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_, lean_object* v___y_6230_, lean_object* v___y_6231_, lean_object* v___y_6232_, lean_object* v___y_6233_){
_start:
{
lean_object* v_res_6234_; 
v_res_6234_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_6220_, v_scope_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_, v___y_6229_, v___y_6230_, v___y_6231_, v___y_6232_);
lean_dec(v___y_6232_);
lean_dec_ref(v___y_6231_);
lean_dec(v___y_6230_);
lean_dec_ref(v___y_6229_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v___y_6226_);
lean_dec_ref(v___y_6225_);
lean_dec(v___y_6224_);
lean_dec(v___y_6223_);
lean_dec_ref(v___y_6222_);
return v_res_6234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_scope_6235_, lean_object* v_goal_6236_, lean_object* v_a_6237_, lean_object* v_a_6238_, lean_object* v_a_6239_, lean_object* v_a_6240_, lean_object* v_a_6241_, lean_object* v_a_6242_, lean_object* v_a_6243_, lean_object* v_a_6244_, lean_object* v_a_6245_, lean_object* v_a_6246_, lean_object* v_a_6247_){
_start:
{
lean_object* v___f_6249_; lean_object* v___x_6250_; 
lean_inc(v_goal_6236_);
v___f_6249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6249_, 0, v_goal_6236_);
lean_closure_set(v___f_6249_, 1, v_scope_6235_);
v___x_6250_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6236_, v___f_6249_, v_a_6237_, v_a_6238_, v_a_6239_, v_a_6240_, v_a_6241_, v_a_6242_, v_a_6243_, v_a_6244_, v_a_6245_, v_a_6246_, v_a_6247_);
return v___x_6250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_scope_6251_, lean_object* v_goal_6252_, lean_object* v_a_6253_, lean_object* v_a_6254_, lean_object* v_a_6255_, lean_object* v_a_6256_, lean_object* v_a_6257_, lean_object* v_a_6258_, lean_object* v_a_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v_a_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_){
_start:
{
lean_object* v_res_6265_; 
v_res_6265_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_6251_, v_goal_6252_, v_a_6253_, v_a_6254_, v_a_6255_, v_a_6256_, v_a_6257_, v_a_6258_, v_a_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_);
lean_dec(v_a_6263_);
lean_dec_ref(v_a_6262_);
lean_dec(v_a_6261_);
lean_dec_ref(v_a_6260_);
lean_dec(v_a_6259_);
lean_dec_ref(v_a_6258_);
lean_dec(v_a_6257_);
lean_dec_ref(v_a_6256_);
lean_dec(v_a_6255_);
lean_dec(v_a_6254_);
lean_dec_ref(v_a_6253_);
return v_res_6265_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(builtin);
}
#ifdef __cplusplus
}
#endif
