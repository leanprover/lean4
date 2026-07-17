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
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEqFast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc;
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_BackwardRule_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\ntarget:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "\nPred:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\nexcessArgs: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "\nrule type:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "spec rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Failed to apply rule "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\nerror: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Failed to construct rule "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Applying spec "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ". Excess args: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object**);
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
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bind"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bind"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 22, 179, 212, 181, 141, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 214, 105, 100, 54, 209, 36, 192)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Pure"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__3_value),LEAN_SCALAR_PTR_LITERAL(121, 135, 27, 238, 232, 181, 75, 85)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__4_value),LEAN_SCALAR_PTR_LITERAL(204, 106, 105, 165, 210, 13, 14, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Functor"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "map"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__6_value),LEAN_SCALAR_PTR_LITERAL(39, 234, 35, 88, 204, 30, 230, 30)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__7_value),LEAN_SCALAR_PTR_LITERAL(64, 222, 215, 42, 158, 211, 169, 226)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Seq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "seq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__9_value),LEAN_SCALAR_PTR_LITERAL(96, 79, 17, 128, 200, 87, 234, 137)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__10_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 8, 167, 199, 144, 196, 104)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "SeqRight"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "seqRight"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__12_value),LEAN_SCALAR_PTR_LITERAL(244, 210, 60, 86, 219, 187, 173, 132)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__14_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__13_value),LEAN_SCALAR_PTR_LITERAL(223, 166, 112, 57, 41, 237, 47, 222)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "SeqLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__15_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "seqLeft"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__15_value),LEAN_SCALAR_PTR_LITERAL(219, 37, 56, 232, 132, 149, 121, 131)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__17_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__16_value),LEAN_SCALAR_PTR_LITERAL(6, 13, 58, 87, 200, 124, 192, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__17_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__14_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__18_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__19_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__8_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__20_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__21_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__5_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__21_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__22_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__23_value;
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "frame rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "frame: failed to apply rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "`@[frameproc]` matched "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "vcgen: speculative spec application for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = " did not produce goals"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(lean_object* v_msgData_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_137_; lean_object* v_env_138_; lean_object* v___x_139_; lean_object* v_mctx_140_; lean_object* v_lctx_141_; lean_object* v_options_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_137_ = lean_st_ref_get(v___y_135_);
v_env_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc_ref(v_env_138_);
lean_dec(v___x_137_);
v___x_139_ = lean_st_ref_get(v___y_133_);
v_mctx_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_mctx_140_);
lean_dec(v___x_139_);
v_lctx_141_ = lean_ctor_get(v___y_132_, 2);
v_options_142_ = lean_ctor_get(v___y_134_, 2);
lean_inc_ref(v_options_142_);
lean_inc_ref(v_lctx_141_);
v___x_143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_143_, 0, v_env_138_);
lean_ctor_set(v___x_143_, 1, v_mctx_140_);
lean_ctor_set(v___x_143_, 2, v_lctx_141_);
lean_ctor_set(v___x_143_, 3, v_options_142_);
v___x_144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_msgData_131_);
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0___boxed(lean_object* v_msgData_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msgData_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(lean_object* v_msg_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_ref_159_; lean_object* v___x_160_; lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_ref_159_ = lean_ctor_get(v___y_156_, 5);
v___x_160_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
v_a_161_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v___x_160_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_160_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
lean_inc(v_ref_159_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v_ref_159_);
lean_ctor_set(v___x_165_, 1, v_a_161_);
if (v_isShared_164_ == 0)
{
lean_ctor_set_tag(v___x_163_, 1);
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg___boxed(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1));
v___x_181_ = l_Lean_stringToMessageData(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(lean_object* v_goal_184_, lean_object* v_target_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___y_199_; uint8_t v___x_204_; 
v___x_204_ = l_Lean_Expr_isForall(v_target_185_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_goal_184_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; 
lean_inc(v_goal_184_);
v___x_207_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_184_, v_a_186_, v_a_187_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_258_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_258_ == 0)
{
v___x_210_ = v___x_207_;
v_isShared_211_ = v_isSharedCheck_258_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_207_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_258_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v_fst_213_; uint8_t v_snd_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_218_; lean_object* v___y_219_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_224_; lean_object* v___y_225_; 
switch(lean_obj_tag(v_a_208_))
{
case 0:
{
uint8_t v___x_252_; 
lean_del_object(v___x_210_);
v___x_252_ = 0;
v_fst_213_ = v_goal_184_;
v_snd_214_ = v___x_252_;
v___y_215_ = v_a_186_;
v___y_216_ = v_a_187_;
v___y_217_ = v_a_188_;
v___y_218_ = v_a_189_;
v___y_219_ = v_a_190_;
v___y_220_ = v_a_191_;
v___y_221_ = v_a_192_;
v___y_222_ = v_a_193_;
v___y_223_ = v_a_194_;
v___y_224_ = v_a_195_;
v___y_225_ = v_a_196_;
goto v___jp_212_;
}
case 1:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
lean_dec(v_goal_184_);
v___x_253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_211_ == 0)
{
lean_ctor_set(v___x_210_, 0, v___x_253_);
v___x_255_ = v___x_210_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
default: 
{
lean_object* v_mvarId_257_; 
lean_del_object(v___x_210_);
lean_dec(v_goal_184_);
v_mvarId_257_ = lean_ctor_get(v_a_208_, 0);
lean_inc(v_mvarId_257_);
lean_dec_ref_known(v_a_208_, 1);
v_fst_213_ = v_mvarId_257_;
v_snd_214_ = v___x_204_;
v___y_215_ = v_a_186_;
v___y_216_ = v_a_187_;
v___y_217_ = v_a_188_;
v___y_218_ = v_a_189_;
v___y_219_ = v_a_190_;
v___y_220_ = v_a_191_;
v___y_221_ = v_a_192_;
v___y_222_ = v_a_193_;
v___y_223_ = v_a_194_;
v___y_224_ = v_a_195_;
v___y_225_ = v_a_196_;
goto v___jp_212_;
}
}
v___jp_212_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
lean_inc(v_fst_213_);
v___x_227_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_fst_213_, v___x_226_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
if (lean_obj_tag(v___x_227_) == 0)
{
if (v_snd_214_ == 0)
{
if (v___x_204_ == 0)
{
lean_object* v_a_228_; 
lean_dec(v_fst_213_);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___y_199_ = v_a_228_;
goto v___jp_198_;
}
else
{
lean_object* v_a_229_; uint8_t v___x_230_; 
v_a_229_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_227_, 1);
v___x_230_ = l_Lean_instBEqMVarId_beq(v_a_229_, v_fst_213_);
if (v___x_230_ == 0)
{
lean_dec(v_fst_213_);
v___y_199_ = v_a_229_;
goto v___jp_198_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_242_; 
lean_dec(v_a_229_);
v___x_231_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v_fst_213_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_233_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_242_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_242_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_a_235_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
}
}
}
else
{
lean_object* v_a_243_; 
lean_dec(v_fst_213_);
v_a_243_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_227_, 1);
v___y_199_ = v_a_243_;
goto v___jp_198_;
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v_fst_213_);
v_a_244_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_227_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_227_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
else
{
lean_object* v_a_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_266_; 
lean_dec(v_goal_184_);
v_a_259_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_266_ == 0)
{
v___x_261_ = v___x_207_;
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_a_259_);
lean_dec(v___x_207_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_266_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_262_ == 0)
{
v___x_264_ = v___x_261_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_a_259_);
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
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_201_, 0, v___y_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___boxed(lean_object* v_goal_267_, lean_object* v_target_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_267_, v_target_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_, v_a_278_, v_a_279_);
lean_dec(v_a_279_);
lean_dec_ref(v_a_278_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
lean_dec(v_a_271_);
lean_dec(v_a_270_);
lean_dec_ref(v_a_269_);
lean_dec_ref(v_target_268_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(lean_object* v_00_u03b1_282_, lean_object* v_msg_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_283_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___boxed(lean_object* v_00_u03b1_297_, lean_object* v_msg_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(v_00_u03b1_297_, v_msg_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
return v_res_311_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0));
v___x_314_ = l_Lean_stringToMessageData(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__2));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(lean_object* v_name_318_, lean_object* v_val_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_useJP_329_; 
v_useJP_329_ = lean_ctor_get_uint8(v_a_320_, sizeof(void*)*6 + 1);
if (v_useJP_329_ == 0)
{
lean_dec(v_name_318_);
goto v___jp_326_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = l_Lean_Elab_Tactic_Do_isJP(v_name_318_);
if (v___x_330_ == 0)
{
lean_dec(v_name_318_);
goto v___jp_326_;
}
else
{
uint8_t v___x_331_; 
v___x_331_ = l_Lean_Expr_isLambda(v_val_319_);
if (v___x_331_ == 0)
{
lean_dec(v_name_318_);
goto v___jp_326_;
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_332_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1);
v___x_333_ = l_Lean_MessageData_ofName(v_name_318_);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_336_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_337_;
}
}
}
v___jp_326_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_box(0);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___boxed(lean_object* v_name_338_, lean_object* v_val_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_name_338_, v_val_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec_ref(v_a_341_);
lean_dec_ref(v_a_340_);
lean_dec_ref(v_val_339_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(lean_object* v_name_347_, lean_object* v_val_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_name_347_, v_val_348_, v_a_349_, v_a_356_, v_a_357_, v_a_358_, v_a_359_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___boxed(lean_object* v_name_362_, lean_object* v_val_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(v_name_362_, v_val_363_, v_a_364_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec_ref(v_a_367_);
lean_dec(v_a_366_);
lean_dec(v_a_365_);
lean_dec_ref(v_a_364_);
lean_dec_ref(v_val_363_);
return v_res_376_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_377_; double v___x_378_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v___x_378_ = lean_float_of_nat(v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object* v_cls_382_, lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_ref_389_; lean_object* v___x_390_; lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_435_; 
v_ref_389_ = lean_ctor_get(v___y_386_, 5);
v___x_390_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
v_a_391_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_435_ == 0)
{
v___x_393_ = v___x_390_;
v_isShared_394_ = v_isSharedCheck_435_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_390_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_435_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v_traceState_396_; lean_object* v_env_397_; lean_object* v_nextMacroScope_398_; lean_object* v_ngen_399_; lean_object* v_auxDeclNGen_400_; lean_object* v_cache_401_; lean_object* v_messages_402_; lean_object* v_infoState_403_; lean_object* v_snapshotTasks_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_434_; 
v___x_395_ = lean_st_ref_take(v___y_387_);
v_traceState_396_ = lean_ctor_get(v___x_395_, 4);
v_env_397_ = lean_ctor_get(v___x_395_, 0);
v_nextMacroScope_398_ = lean_ctor_get(v___x_395_, 1);
v_ngen_399_ = lean_ctor_get(v___x_395_, 2);
v_auxDeclNGen_400_ = lean_ctor_get(v___x_395_, 3);
v_cache_401_ = lean_ctor_get(v___x_395_, 5);
v_messages_402_ = lean_ctor_get(v___x_395_, 6);
v_infoState_403_ = lean_ctor_get(v___x_395_, 7);
v_snapshotTasks_404_ = lean_ctor_get(v___x_395_, 8);
v_isSharedCheck_434_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_434_ == 0)
{
v___x_406_ = v___x_395_;
v_isShared_407_ = v_isSharedCheck_434_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snapshotTasks_404_);
lean_inc(v_infoState_403_);
lean_inc(v_messages_402_);
lean_inc(v_cache_401_);
lean_inc(v_traceState_396_);
lean_inc(v_auxDeclNGen_400_);
lean_inc(v_ngen_399_);
lean_inc(v_nextMacroScope_398_);
lean_inc(v_env_397_);
lean_dec(v___x_395_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_434_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint64_t v_tid_408_; lean_object* v_traces_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_433_; 
v_tid_408_ = lean_ctor_get_uint64(v_traceState_396_, sizeof(void*)*1);
v_traces_409_ = lean_ctor_get(v_traceState_396_, 0);
v_isSharedCheck_433_ = !lean_is_exclusive(v_traceState_396_);
if (v_isSharedCheck_433_ == 0)
{
v___x_411_ = v_traceState_396_;
v_isShared_412_ = v_isSharedCheck_433_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_traces_409_);
lean_dec(v_traceState_396_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_433_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; double v___x_414_; uint8_t v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_413_ = lean_box(0);
v___x_414_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0);
v___x_415_ = 0;
v___x_416_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1));
v___x_417_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_417_, 0, v_cls_382_);
lean_ctor_set(v___x_417_, 1, v___x_413_);
lean_ctor_set(v___x_417_, 2, v___x_416_);
lean_ctor_set_float(v___x_417_, sizeof(void*)*3, v___x_414_);
lean_ctor_set_float(v___x_417_, sizeof(void*)*3 + 8, v___x_414_);
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*3 + 16, v___x_415_);
v___x_418_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2));
v___x_419_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v_a_391_);
lean_ctor_set(v___x_419_, 2, v___x_418_);
lean_inc(v_ref_389_);
v___x_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_420_, 0, v_ref_389_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
v___x_421_ = l_Lean_PersistentArray_push___redArg(v_traces_409_, v___x_420_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_421_);
v___x_423_ = v___x_411_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_421_);
lean_ctor_set_uint64(v_reuseFailAlloc_432_, sizeof(void*)*1, v_tid_408_);
v___x_423_ = v_reuseFailAlloc_432_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 4, v___x_423_);
v___x_425_ = v___x_406_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_env_397_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_nextMacroScope_398_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_ngen_399_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_auxDeclNGen_400_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v___x_423_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_cache_401_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v_messages_402_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_infoState_403_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_snapshotTasks_404_);
v___x_425_ = v_reuseFailAlloc_431_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_426_ = lean_st_ref_set(v___y_387_, v___x_425_);
v___x_427_ = lean_box(0);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_427_);
v___x_429_ = v___x_393_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object* v_cls_436_, lean_object* v_msg_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_436_, v_msg_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
return v_res_443_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_457_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__6));
v___x_458_ = l_Lean_Name_append(v___x_457_, v___x_456_);
return v___x_458_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__8));
v___x_461_ = l_Lean_stringToMessageData(v___x_460_);
return v___x_461_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__10));
v___x_464_ = l_Lean_stringToMessageData(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(lean_object* v_goal_465_, lean_object* v_target_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v___y_480_; lean_object* v___y_481_; lean_object* v___y_482_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; 
if (lean_obj_tag(v_target_466_) == 8)
{
lean_object* v_declName_510_; lean_object* v_value_511_; lean_object* v_body_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___x_551_; 
v_declName_510_ = lean_ctor_get(v_target_466_, 0);
lean_inc_n(v_declName_510_, 2);
v_value_511_ = lean_ctor_get(v_target_466_, 2);
lean_inc_ref(v_value_511_);
v_body_512_ = lean_ctor_get(v_target_466_, 3);
lean_inc_ref(v_body_512_);
lean_dec_ref_known(v_target_466_, 4);
v___x_551_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_510_, v_value_511_, v_a_467_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_551_) == 0)
{
uint8_t v___x_552_; 
lean_dec_ref_known(v___x_551_, 1);
v___x_552_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_511_);
if (v___x_552_ == 0)
{
lean_object* v_options_553_; uint8_t v_hasTrace_554_; 
lean_dec_ref(v_body_512_);
lean_dec_ref(v_value_511_);
v_options_553_ = lean_ctor_get(v_a_476_, 2);
v_hasTrace_554_ = lean_ctor_get_uint8(v_options_553_, sizeof(void*)*1);
if (v_hasTrace_554_ == 0)
{
lean_dec(v_declName_510_);
v___y_480_ = v_a_467_;
v___y_481_ = v_a_468_;
v___y_482_ = v_a_469_;
v___y_483_ = v_a_470_;
v___y_484_ = v_a_471_;
v___y_485_ = v_a_472_;
v___y_486_ = v_a_473_;
v___y_487_ = v_a_474_;
v___y_488_ = v_a_475_;
v___y_489_ = v_a_476_;
v___y_490_ = v_a_477_;
goto v___jp_479_;
}
else
{
lean_object* v_inheritedTraceOptions_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_inheritedTraceOptions_555_ = lean_ctor_get(v_a_476_, 13);
v___x_556_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_557_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_555_, v_options_553_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_declName_510_);
v___y_480_ = v_a_467_;
v___y_481_ = v_a_468_;
v___y_482_ = v_a_469_;
v___y_483_ = v_a_470_;
v___y_484_ = v_a_471_;
v___y_485_ = v_a_472_;
v___y_486_ = v_a_473_;
v___y_487_ = v_a_474_;
v___y_488_ = v_a_475_;
v___y_489_ = v_a_476_;
v___y_490_ = v_a_477_;
goto v___jp_479_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_559_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9);
v___x_560_ = l_Lean_MessageData_ofName(v_declName_510_);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_556_, v___x_561_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_dec_ref_known(v___x_562_, 1);
v___y_480_ = v_a_467_;
v___y_481_ = v_a_468_;
v___y_482_ = v_a_469_;
v___y_483_ = v_a_470_;
v___y_484_ = v_a_471_;
v___y_485_ = v_a_472_;
v___y_486_ = v_a_473_;
v___y_487_ = v_a_474_;
v___y_488_ = v_a_475_;
v___y_489_ = v_a_476_;
v___y_490_ = v_a_477_;
goto v___jp_479_;
}
else
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_570_; 
lean_dec(v_goal_465_);
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_570_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_570_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
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
}
}
else
{
lean_object* v_options_571_; uint8_t v_hasTrace_572_; 
v_options_571_ = lean_ctor_get(v_a_476_, 2);
v_hasTrace_572_ = lean_ctor_get_uint8(v_options_571_, sizeof(void*)*1);
if (v_hasTrace_572_ == 0)
{
lean_dec(v_declName_510_);
v___y_514_ = v_a_472_;
v___y_515_ = v_a_473_;
v___y_516_ = v_a_474_;
v___y_517_ = v_a_475_;
v___y_518_ = v_a_476_;
v___y_519_ = v_a_477_;
goto v___jp_513_;
}
else
{
lean_object* v_inheritedTraceOptions_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_inheritedTraceOptions_573_ = lean_ctor_get(v_a_476_, 13);
v___x_574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_575_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_576_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_573_, v_options_571_, v___x_575_);
if (v___x_576_ == 0)
{
lean_dec(v_declName_510_);
v___y_514_ = v_a_472_;
v___y_515_ = v_a_473_;
v___y_516_ = v_a_474_;
v___y_517_ = v_a_475_;
v___y_518_ = v_a_476_;
v___y_519_ = v_a_477_;
goto v___jp_513_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_578_ = l_Lean_MessageData_ofName(v_declName_510_);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_574_, v___x_579_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_dec_ref_known(v___x_580_, 1);
v___y_514_ = v_a_472_;
v___y_515_ = v_a_473_;
v___y_516_ = v_a_474_;
v___y_517_ = v_a_475_;
v___y_518_ = v_a_476_;
v___y_519_ = v_a_477_;
goto v___jp_513_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_body_512_);
lean_dec_ref(v_value_511_);
lean_dec(v_goal_465_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec_ref(v_body_512_);
lean_dec_ref(v_value_511_);
lean_dec(v_declName_510_);
lean_dec(v_goal_465_);
v_a_589_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_551_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_551_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
v___jp_513_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_mk_empty_array_with_capacity(v___x_520_);
v___x_522_ = lean_array_push(v___x_521_, v_value_511_);
v___x_523_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_512_, v___x_522_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_465_, v_a_524_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_534_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_528_ = v___x_525_;
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_a_526_);
lean_dec(v___x_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_534_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v_a_526_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_530_);
v___x_532_ = v___x_528_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
v_a_535_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_525_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_525_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v_goal_465_);
v_a_543_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___x_523_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___x_523_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
else
{
lean_object* v___x_597_; lean_object* v___x_598_; 
lean_dec_ref(v_target_466_);
lean_dec(v_goal_465_);
v___x_597_ = lean_box(0);
v___x_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
return v___x_598_;
}
v___jp_479_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_492_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_goal_465_, v___x_491_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_501_; 
v_a_493_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_501_ == 0)
{
v___x_495_ = v___x_492_;
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_501_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v_a_493_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_499_ = v___x_495_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_492_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_492_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_492_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_492_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___boxed(lean_object* v_goal_599_, lean_object* v_target_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_599_, v_target_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_, v_a_611_);
lean_dec(v_a_611_);
lean_dec_ref(v_a_610_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
lean_dec(v_a_605_);
lean_dec_ref(v_a_604_);
lean_dec(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(lean_object* v_cls_614_, lean_object* v_msg_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_614_, v_msg_615_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object* v_cls_629_, lean_object* v_msg_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(v_cls_629_, v_msg_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(lean_object* v_goal_652_, lean_object* v_target_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3));
v___x_667_ = l_Lean_Expr_isAppOf(v_target_653_, v___x_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v_goal_652_);
v___x_668_ = lean_box(0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
else
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(v_goal_652_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_, v_a_664_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_a_671_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_670_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_670_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_688_, lean_object* v_target_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_688_, v_target_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
lean_dec(v_a_692_);
lean_dec(v_a_691_);
lean_dec_ref(v_a_690_);
lean_dec_ref(v_target_689_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_x_706_){
_start:
{
lean_object* v_ks_707_; lean_object* v_vs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_732_; 
v_ks_707_ = lean_ctor_get(v_x_703_, 0);
v_vs_708_ = lean_ctor_get(v_x_703_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_x_703_);
if (v_isSharedCheck_732_ == 0)
{
v___x_710_ = v_x_703_;
v_isShared_711_ = v_isSharedCheck_732_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_vs_708_);
lean_inc(v_ks_707_);
lean_dec(v_x_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_732_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_712_ = lean_array_get_size(v_ks_707_);
v___x_713_ = lean_nat_dec_lt(v_x_704_, v___x_712_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
lean_dec(v_x_704_);
v___x_714_ = lean_array_push(v_ks_707_, v_x_705_);
v___x_715_ = lean_array_push(v_vs_708_, v_x_706_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_715_);
lean_ctor_set(v___x_710_, 0, v___x_714_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
else
{
lean_object* v_k_x27_719_; uint8_t v___x_720_; 
v_k_x27_719_ = lean_array_fget_borrowed(v_ks_707_, v_x_704_);
v___x_720_ = l_Lean_instBEqMVarId_beq(v_x_705_, v_k_x27_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_722_; 
if (v_isShared_711_ == 0)
{
v___x_722_ = v___x_710_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_ks_707_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_vs_708_);
v___x_722_ = v_reuseFailAlloc_726_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = lean_unsigned_to_nat(1u);
v___x_724_ = lean_nat_add(v_x_704_, v___x_723_);
lean_dec(v_x_704_);
v_x_703_ = v___x_722_;
v_x_704_ = v___x_724_;
goto _start;
}
}
else
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v___x_727_ = lean_array_fset(v_ks_707_, v_x_704_, v_x_705_);
v___x_728_ = lean_array_fset(v_vs_708_, v_x_704_, v_x_706_);
lean_dec(v_x_704_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 1, v___x_728_);
lean_ctor_set(v___x_710_, 0, v___x_727_);
v___x_730_ = v___x_710_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_733_, lean_object* v_k_734_, lean_object* v_v_735_){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_unsigned_to_nat(0u);
v___x_737_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_733_, v___x_736_, v_k_734_, v_v_735_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_739_, size_t v_x_740_, size_t v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v_es_744_; size_t v___x_745_; size_t v___x_746_; lean_object* v_j_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_es_744_ = lean_ctor_get(v_x_739_, 0);
v___x_745_ = ((size_t)31ULL);
v___x_746_ = lean_usize_land(v_x_740_, v___x_745_);
v_j_747_ = lean_usize_to_nat(v___x_746_);
v___x_748_ = lean_array_get_size(v_es_744_);
v___x_749_ = lean_nat_dec_lt(v_j_747_, v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v_j_747_);
lean_dec(v_x_743_);
lean_dec(v_x_742_);
return v_x_739_;
}
else
{
lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_788_; 
lean_inc_ref(v_es_744_);
v_isSharedCheck_788_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_x_739_, 0);
lean_dec(v_unused_789_);
v___x_751_ = v_x_739_;
v_isShared_752_ = v_isSharedCheck_788_;
goto v_resetjp_750_;
}
else
{
lean_dec(v_x_739_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_788_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_v_753_; lean_object* v___x_754_; lean_object* v_xs_x27_755_; lean_object* v___y_757_; 
v_v_753_ = lean_array_fget(v_es_744_, v_j_747_);
v___x_754_ = lean_box(0);
v_xs_x27_755_ = lean_array_fset(v_es_744_, v_j_747_, v___x_754_);
switch(lean_obj_tag(v_v_753_))
{
case 0:
{
lean_object* v_key_762_; lean_object* v_val_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_773_; 
v_key_762_ = lean_ctor_get(v_v_753_, 0);
v_val_763_ = lean_ctor_get(v_v_753_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_v_753_);
if (v_isSharedCheck_773_ == 0)
{
v___x_765_ = v_v_753_;
v_isShared_766_ = v_isSharedCheck_773_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_val_763_);
lean_inc(v_key_762_);
lean_dec(v_v_753_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_773_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_instBEqMVarId_beq(v_x_742_, v_key_762_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_del_object(v___x_765_);
v___x_768_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_762_, v_val_763_, v_x_742_, v_x_743_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
v___y_757_ = v___x_769_;
goto v___jp_756_;
}
else
{
lean_object* v___x_771_; 
lean_dec(v_val_763_);
lean_dec(v_key_762_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_x_743_);
lean_ctor_set(v___x_765_, 0, v_x_742_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_x_742_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_x_743_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v___y_757_ = v___x_771_;
goto v___jp_756_;
}
}
}
}
case 1:
{
lean_object* v_node_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
v_node_774_ = lean_ctor_get(v_v_753_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v_v_753_);
if (v_isSharedCheck_786_ == 0)
{
v___x_776_ = v_v_753_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_node_774_);
lean_dec(v_v_753_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
size_t v___x_778_; size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_778_ = ((size_t)5ULL);
v___x_779_ = lean_usize_shift_right(v_x_740_, v___x_778_);
v___x_780_ = ((size_t)1ULL);
v___x_781_ = lean_usize_add(v_x_741_, v___x_780_);
v___x_782_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_774_, v___x_779_, v___x_781_, v_x_742_, v_x_743_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_782_);
v___x_784_ = v___x_776_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
v___y_757_ = v___x_784_;
goto v___jp_756_;
}
}
}
default: 
{
lean_object* v___x_787_; 
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_x_742_);
lean_ctor_set(v___x_787_, 1, v_x_743_);
v___y_757_ = v___x_787_;
goto v___jp_756_;
}
}
v___jp_756_:
{
lean_object* v___x_758_; lean_object* v___x_760_; 
v___x_758_ = lean_array_fset(v_xs_x27_755_, v_j_747_, v___y_757_);
lean_dec(v_j_747_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_758_);
v___x_760_ = v___x_751_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
lean_object* v_ks_790_; lean_object* v_vs_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_811_; 
v_ks_790_ = lean_ctor_get(v_x_739_, 0);
v_vs_791_ = lean_ctor_get(v_x_739_, 1);
v_isSharedCheck_811_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_811_ == 0)
{
v___x_793_ = v_x_739_;
v_isShared_794_ = v_isSharedCheck_811_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_vs_791_);
lean_inc(v_ks_790_);
lean_dec(v_x_739_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_811_;
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
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_ks_790_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_vs_791_);
v___x_796_ = v_reuseFailAlloc_810_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v_newNode_797_; uint8_t v___y_799_; size_t v___x_805_; uint8_t v___x_806_; 
v_newNode_797_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_796_, v_x_742_, v_x_743_);
v___x_805_ = ((size_t)7ULL);
v___x_806_ = lean_usize_dec_le(v___x_805_, v_x_741_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_807_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_797_);
v___x_808_ = lean_unsigned_to_nat(4u);
v___x_809_ = lean_nat_dec_lt(v___x_807_, v___x_808_);
lean_dec(v___x_807_);
v___y_799_ = v___x_809_;
goto v___jp_798_;
}
else
{
v___y_799_ = v___x_806_;
goto v___jp_798_;
}
v___jp_798_:
{
if (v___y_799_ == 0)
{
lean_object* v_ks_800_; lean_object* v_vs_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_ks_800_ = lean_ctor_get(v_newNode_797_, 0);
lean_inc_ref(v_ks_800_);
v_vs_801_ = lean_ctor_get(v_newNode_797_, 1);
lean_inc_ref(v_vs_801_);
lean_dec_ref(v_newNode_797_);
v___x_802_ = lean_unsigned_to_nat(0u);
v___x_803_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_741_, v_ks_800_, v_vs_801_, v___x_802_, v___x_803_);
lean_dec_ref(v_vs_801_);
lean_dec_ref(v_ks_800_);
return v___x_804_;
}
else
{
return v_newNode_797_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_812_, lean_object* v_keys_813_, lean_object* v_vals_814_, lean_object* v_i_815_, lean_object* v_entries_816_){
_start:
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_array_get_size(v_keys_813_);
v___x_818_ = lean_nat_dec_lt(v_i_815_, v___x_817_);
if (v___x_818_ == 0)
{
lean_dec(v_i_815_);
return v_entries_816_;
}
else
{
lean_object* v_k_819_; lean_object* v_v_820_; uint64_t v___x_821_; size_t v_h_822_; size_t v___x_823_; lean_object* v___x_824_; size_t v___x_825_; size_t v___x_826_; size_t v___x_827_; size_t v_h_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_k_819_ = lean_array_fget_borrowed(v_keys_813_, v_i_815_);
v_v_820_ = lean_array_fget_borrowed(v_vals_814_, v_i_815_);
v___x_821_ = l_Lean_instHashableMVarId_hash(v_k_819_);
v_h_822_ = lean_uint64_to_usize(v___x_821_);
v___x_823_ = ((size_t)5ULL);
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = ((size_t)1ULL);
v___x_826_ = lean_usize_sub(v_depth_812_, v___x_825_);
v___x_827_ = lean_usize_mul(v___x_823_, v___x_826_);
v_h_828_ = lean_usize_shift_right(v_h_822_, v___x_827_);
v___x_829_ = lean_nat_add(v_i_815_, v___x_824_);
lean_dec(v_i_815_);
lean_inc(v_v_820_);
lean_inc(v_k_819_);
v___x_830_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_816_, v_h_828_, v_depth_812_, v_k_819_, v_v_820_);
v_i_815_ = v___x_829_;
v_entries_816_ = v___x_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_832_, lean_object* v_keys_833_, lean_object* v_vals_834_, lean_object* v_i_835_, lean_object* v_entries_836_){
_start:
{
size_t v_depth_boxed_837_; lean_object* v_res_838_; 
v_depth_boxed_837_ = lean_unbox_usize(v_depth_832_);
lean_dec(v_depth_832_);
v_res_838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_837_, v_keys_833_, v_vals_834_, v_i_835_, v_entries_836_);
lean_dec_ref(v_vals_834_);
lean_dec_ref(v_keys_833_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_839_, lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_x_842_, lean_object* v_x_843_){
_start:
{
size_t v_x_8514__boxed_844_; size_t v_x_8515__boxed_845_; lean_object* v_res_846_; 
v_x_8514__boxed_844_ = lean_unbox_usize(v_x_840_);
lean_dec(v_x_840_);
v_x_8515__boxed_845_ = lean_unbox_usize(v_x_841_);
lean_dec(v_x_841_);
v_res_846_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_839_, v_x_8514__boxed_844_, v_x_8515__boxed_845_, v_x_842_, v_x_843_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_x_849_){
_start:
{
uint64_t v___x_850_; size_t v___x_851_; size_t v___x_852_; lean_object* v___x_853_; 
v___x_850_ = l_Lean_instHashableMVarId_hash(v_x_848_);
v___x_851_ = lean_uint64_to_usize(v___x_850_);
v___x_852_ = ((size_t)1ULL);
v___x_853_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_847_, v___x_851_, v___x_852_, v_x_848_, v_x_849_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_854_, lean_object* v_val_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v_mctx_859_; lean_object* v_cache_860_; lean_object* v_zetaDeltaFVarIds_861_; lean_object* v_postponed_862_; lean_object* v_diag_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_891_; 
v___x_858_ = lean_st_ref_take(v___y_856_);
v_mctx_859_ = lean_ctor_get(v___x_858_, 0);
v_cache_860_ = lean_ctor_get(v___x_858_, 1);
v_zetaDeltaFVarIds_861_ = lean_ctor_get(v___x_858_, 2);
v_postponed_862_ = lean_ctor_get(v___x_858_, 3);
v_diag_863_ = lean_ctor_get(v___x_858_, 4);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_891_ == 0)
{
v___x_865_ = v___x_858_;
v_isShared_866_ = v_isSharedCheck_891_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_diag_863_);
lean_inc(v_postponed_862_);
lean_inc(v_zetaDeltaFVarIds_861_);
lean_inc(v_cache_860_);
lean_inc(v_mctx_859_);
lean_dec(v___x_858_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_891_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v_depth_867_; lean_object* v_levelAssignDepth_868_; lean_object* v_lmvarCounter_869_; lean_object* v_mvarCounter_870_; lean_object* v_lDecls_871_; lean_object* v_decls_872_; lean_object* v_userNames_873_; lean_object* v_lAssignment_874_; lean_object* v_eAssignment_875_; lean_object* v_dAssignment_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_890_; 
v_depth_867_ = lean_ctor_get(v_mctx_859_, 0);
v_levelAssignDepth_868_ = lean_ctor_get(v_mctx_859_, 1);
v_lmvarCounter_869_ = lean_ctor_get(v_mctx_859_, 2);
v_mvarCounter_870_ = lean_ctor_get(v_mctx_859_, 3);
v_lDecls_871_ = lean_ctor_get(v_mctx_859_, 4);
v_decls_872_ = lean_ctor_get(v_mctx_859_, 5);
v_userNames_873_ = lean_ctor_get(v_mctx_859_, 6);
v_lAssignment_874_ = lean_ctor_get(v_mctx_859_, 7);
v_eAssignment_875_ = lean_ctor_get(v_mctx_859_, 8);
v_dAssignment_876_ = lean_ctor_get(v_mctx_859_, 9);
v_isSharedCheck_890_ = !lean_is_exclusive(v_mctx_859_);
if (v_isSharedCheck_890_ == 0)
{
v___x_878_ = v_mctx_859_;
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_dAssignment_876_);
lean_inc(v_eAssignment_875_);
lean_inc(v_lAssignment_874_);
lean_inc(v_userNames_873_);
lean_inc(v_decls_872_);
lean_inc(v_lDecls_871_);
lean_inc(v_mvarCounter_870_);
lean_inc(v_lmvarCounter_869_);
lean_inc(v_levelAssignDepth_868_);
lean_inc(v_depth_867_);
lean_dec(v_mctx_859_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_890_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_880_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_875_, v_mvarId_854_, v_val_855_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 8, v___x_880_);
v___x_882_ = v___x_878_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_depth_867_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_levelAssignDepth_868_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_lmvarCounter_869_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_mvarCounter_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_lDecls_871_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v_decls_872_);
lean_ctor_set(v_reuseFailAlloc_889_, 6, v_userNames_873_);
lean_ctor_set(v_reuseFailAlloc_889_, 7, v_lAssignment_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 8, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_889_, 9, v_dAssignment_876_);
v___x_882_ = v_reuseFailAlloc_889_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_884_; 
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_882_);
v___x_884_ = v___x_865_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_cache_860_);
lean_ctor_set(v_reuseFailAlloc_888_, 2, v_zetaDeltaFVarIds_861_);
lean_ctor_set(v_reuseFailAlloc_888_, 3, v_postponed_862_);
lean_ctor_set(v_reuseFailAlloc_888_, 4, v_diag_863_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_885_ = lean_st_ref_set(v___y_856_, v___x_884_);
v___x_886_ = lean_box(0);
v___x_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
return v___x_887_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_892_, lean_object* v_val_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_892_, v_val_893_, v___y_894_);
lean_dec(v___y_894_);
return v_res_896_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = l_Lean_Level_ofNat(v___x_904_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4);
v___x_907_ = l_Lean_mkSort(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5);
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6);
v___x_912_ = lean_unsigned_to_nat(2u);
v___x_913_ = lean_mk_empty_array_with_capacity(v___x_912_);
v___x_914_ = lean_array_push(v___x_913_, v___x_911_);
v___x_915_ = lean_array_push(v___x_914_, v___x_910_);
return v___x_915_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
v___x_929_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12));
v___x_930_ = l_Lean_mkConst(v___x_929_, v___x_928_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(lean_object* v_goal_931_, lean_object* v_target_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v___x_945_; 
lean_inc_ref(v_target_932_);
v___x_945_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(v_target_932_);
if (lean_obj_tag(v___x_945_) == 1)
{
lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1012_; 
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v___x_945_, 0);
lean_dec(v_unused_1013_);
v___x_947_ = v___x_945_;
v_isShared_948_ = v_isSharedCheck_1012_;
goto v_resetjp_946_;
}
else
{
lean_dec(v___x_945_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1012_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_950_ = lean_unsigned_to_nat(2u);
v___x_951_ = lean_mk_empty_array_with_capacity(v___x_950_);
v___x_952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7);
v___x_953_ = l_Lean_Meta_mkAppOptM(v___x_949_, v___x_952_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc(v_a_954_);
lean_dec_ref_known(v___x_953_, 1);
v___x_955_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_956_ = lean_array_push(v___x_951_, v_a_954_);
lean_inc_ref(v_target_932_);
v___x_957_ = lean_array_push(v___x_956_, v_target_932_);
v___x_958_ = l_Lean_Meta_mkAppM(v___x_955_, v___x_957_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = l_Lean_Meta_Sym_shareCommon(v_a_959_, v_a_938_, v_a_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = lean_box(0);
v___x_963_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_961_, v___x_962_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_978_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc_n(v_a_964_, 2);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13);
v___x_966_ = l_Lean_mkAppB(v___x_965_, v_target_932_, v_a_964_);
v___x_967_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_931_, v___x_966_, v_a_941_);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_978_ == 0)
{
lean_object* v_unused_979_; 
v_unused_979_ = lean_ctor_get(v___x_967_, 0);
lean_dec(v_unused_979_);
v___x_969_ = v___x_967_;
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
else
{
lean_dec(v___x_967_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_978_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = l_Lean_Expr_mvarId_x21(v_a_964_);
lean_dec(v_a_964_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_971_);
v___x_973_ = v___x_947_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v___x_971_);
v___x_973_ = v_reuseFailAlloc_977_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
lean_object* v___x_975_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_973_);
v___x_975_ = v___x_969_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v___x_973_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_del_object(v___x_947_);
lean_dec_ref(v_target_932_);
lean_dec(v_goal_931_);
v_a_980_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_963_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_963_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_del_object(v___x_947_);
lean_dec_ref(v_target_932_);
lean_dec(v_goal_931_);
v_a_988_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_960_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_960_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_del_object(v___x_947_);
lean_dec_ref(v_target_932_);
lean_dec(v_goal_931_);
v_a_996_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_958_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_958_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v___x_951_);
lean_del_object(v___x_947_);
lean_dec_ref(v_target_932_);
lean_dec(v_goal_931_);
v_a_1004_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_953_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_953_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; 
lean_dec(v___x_945_);
lean_dec_ref(v_target_932_);
lean_dec(v_goal_931_);
v___x_1014_ = lean_box(0);
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1016_, lean_object* v_target_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_1016_, v_target_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
lean_dec(v_a_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_a_1024_);
lean_dec_ref(v_a_1023_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec(v_a_1019_);
lean_dec_ref(v_a_1018_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1031_, lean_object* v_val_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1031_, v_val_1032_, v___y_1041_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1046_, lean_object* v_val_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1046_, v_val_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v___y_1054_);
lean_dec_ref(v___y_1053_);
lean_dec(v___y_1052_);
lean_dec_ref(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1066_, lean_object* v_x_1067_, size_t v_x_1068_, size_t v_x_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1067_, v_x_1068_, v_x_1069_, v_x_1070_, v_x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1073_, lean_object* v_x_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
size_t v_x_9024__boxed_1079_; size_t v_x_9025__boxed_1080_; lean_object* v_res_1081_; 
v_x_9024__boxed_1079_ = lean_unbox_usize(v_x_1075_);
lean_dec(v_x_1075_);
v_x_9025__boxed_1080_ = lean_unbox_usize(v_x_1076_);
lean_dec(v_x_1076_);
v_res_1081_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1073_, v_x_1074_, v_x_9024__boxed_1079_, v_x_9025__boxed_1080_, v_x_1077_, v_x_1078_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1082_, lean_object* v_n_1083_, lean_object* v_k_1084_, lean_object* v_v_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1083_, v_k_1084_, v_v_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1087_, size_t v_depth_1088_, lean_object* v_keys_1089_, lean_object* v_vals_1090_, lean_object* v_heq_1091_, lean_object* v_i_1092_, lean_object* v_entries_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1088_, v_keys_1089_, v_vals_1090_, v_i_1092_, v_entries_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1095_, lean_object* v_depth_1096_, lean_object* v_keys_1097_, lean_object* v_vals_1098_, lean_object* v_heq_1099_, lean_object* v_i_1100_, lean_object* v_entries_1101_){
_start:
{
size_t v_depth_boxed_1102_; lean_object* v_res_1103_; 
v_depth_boxed_1102_ = lean_unbox_usize(v_depth_1096_);
lean_dec(v_depth_1096_);
v_res_1103_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1095_, v_depth_boxed_1102_, v_keys_1097_, v_vals_1098_, v_heq_1099_, v_i_1100_, v_entries_1101_);
lean_dec_ref(v_vals_1098_);
lean_dec_ref(v_keys_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1104_, lean_object* v_x_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0));
v___x_1112_ = l_Lean_stringToMessageData(v___x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(lean_object* v_goal_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_){
_start:
{
lean_object* v_backwardRules_1122_; lean_object* v_refl_1123_; lean_object* v___x_1124_; 
v_backwardRules_1122_ = lean_ctor_get(v_a_1114_, 0);
v_refl_1123_ = lean_ctor_get(v_backwardRules_1122_, 7);
lean_inc_ref(v_refl_1123_);
lean_inc(v_goal_1113_);
v___x_1124_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1113_, v_refl_1123_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1163_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1163_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1163_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
if (lean_obj_tag(v_a_1125_) == 1)
{
lean_object* v_mvarIds_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1158_; 
v_mvarIds_1129_ = lean_ctor_get(v_a_1125_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_a_1125_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1131_ = v_a_1125_;
v_isShared_1132_ = v_isSharedCheck_1158_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_mvarIds_1129_);
lean_dec(v_a_1125_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1158_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_options_1140_; uint8_t v_hasTrace_1141_; 
v_options_1140_ = lean_ctor_get(v_a_1119_, 2);
v_hasTrace_1141_ = lean_ctor_get_uint8(v_options_1140_, sizeof(void*)*1);
if (v_hasTrace_1141_ == 0)
{
lean_dec(v_goal_1113_);
goto v___jp_1133_;
}
else
{
lean_object* v_inheritedTraceOptions_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; uint8_t v___x_1145_; 
v_inheritedTraceOptions_1142_ = lean_ctor_get(v_a_1119_, 13);
v___x_1143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1145_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1142_, v_options_1140_, v___x_1144_);
if (v___x_1145_ == 0)
{
lean_dec(v_goal_1113_);
goto v___jp_1133_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1146_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_goal_1113_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1143_, v___x_1148_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_dec_ref_known(v___x_1149_, 1);
goto v___jp_1133_;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_del_object(v___x_1131_);
lean_dec(v_mvarIds_1129_);
lean_del_object(v___x_1127_);
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
v___jp_1133_:
{
lean_object* v___x_1135_; 
if (v_isShared_1132_ == 0)
{
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_mvarIds_1129_);
v___x_1135_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
lean_object* v___x_1137_; 
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1135_);
v___x_1137_ = v___x_1127_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec(v_a_1125_);
lean_dec(v_goal_1113_);
v___x_1159_ = lean_box(0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1159_);
v___x_1161_ = v___x_1127_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
lean_dec(v_goal_1113_);
v_a_1164_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1124_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1124_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_a_1179_);
lean_dec(v_a_1179_);
lean_dec_ref(v_a_1178_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec_ref(v_a_1173_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(lean_object* v_goal_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1182_, v_a_1183_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___boxed(lean_object* v_goal_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(v_goal_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_, v_a_1206_, v_a_1207_);
lean_dec(v_a_1207_);
lean_dec_ref(v_a_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
lean_dec(v_a_1199_);
lean_dec(v_a_1198_);
lean_dec_ref(v_a_1197_);
return v_res_1209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1212_ = l_Lean_stringToMessageData(v___x_1211_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1213_, lean_object* v_e_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1220_; 
v_lastLiftedPre_x3f_1220_ = lean_ctor_get(v_scope_1213_, 2);
lean_inc(v_lastLiftedPre_x3f_1220_);
lean_dec_ref(v_scope_1213_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1220_) == 1)
{
lean_object* v_val_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1278_; 
v_val_1221_ = lean_ctor_get(v_lastLiftedPre_x3f_1220_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1220_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1223_ = v_lastLiftedPre_x3f_1220_;
v_isShared_1224_ = v_isSharedCheck_1278_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_val_1221_);
lean_dec(v_lastLiftedPre_x3f_1220_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1278_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v_lctx_1225_; lean_object* v___x_1226_; 
v_lctx_1225_ = lean_ctor_get(v_a_1215_, 2);
lean_inc_ref(v_lctx_1225_);
v___x_1226_ = lean_local_ctx_find(v_lctx_1225_, v_val_1221_);
if (lean_obj_tag(v___x_1226_) == 1)
{
lean_object* v_val_1227_; lean_object* v___x_1228_; size_t v___x_1229_; size_t v___x_1230_; uint8_t v___x_1231_; 
v_val_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1227_);
v___x_1228_ = l_Lean_LocalDecl_type(v_val_1227_);
v___x_1229_ = lean_ptr_addr(v_e_1214_);
v___x_1230_ = lean_ptr_addr(v___x_1228_);
lean_dec_ref(v___x_1228_);
v___x_1231_ = lean_usize_dec_eq(v___x_1229_, v___x_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_val_1227_);
lean_del_object(v___x_1223_);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1239_ == 0)
{
lean_object* v_unused_1240_; 
v_unused_1240_ = lean_ctor_get(v___x_1226_, 0);
lean_dec(v_unused_1240_);
v___x_1233_ = v___x_1226_;
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
else
{
lean_dec(v___x_1226_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1239_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_box(0);
if (v_isShared_1234_ == 0)
{
lean_ctor_set_tag(v___x_1233_, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v_options_1241_; uint8_t v_hasTrace_1242_; 
v_options_1241_ = lean_ctor_get(v_a_1217_, 2);
v_hasTrace_1242_ = lean_ctor_get_uint8(v_options_1241_, sizeof(void*)*1);
if (v_hasTrace_1242_ == 0)
{
lean_object* v___x_1244_; 
lean_dec(v_val_1227_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1244_ = v___x_1223_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1226_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_inheritedTraceOptions_1246_ = lean_ctor_get(v_a_1217_, 13);
v___x_1247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1248_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1249_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1246_, v_options_1241_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1251_; 
lean_dec(v_val_1227_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1226_);
v___x_1251_ = v___x_1223_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1226_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_del_object(v___x_1223_);
v___x_1253_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1254_ = l_Lean_LocalDecl_userName(v_val_1227_);
lean_dec(v_val_1227_);
v___x_1255_ = l_Lean_MessageData_ofName(v___x_1254_);
v___x_1256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1253_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1247_, v___x_1256_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1265_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v___x_1226_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1226_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref_known(v___x_1226_, 1);
v_a_1266_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1257_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1257_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_dec(v___x_1226_);
v___x_1274_ = lean_box(0);
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1274_);
v___x_1276_ = v___x_1223_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_dec(v_lastLiftedPre_x3f_1220_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1281_, lean_object* v_e_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1281_, v_e_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_);
lean_dec(v_a_1286_);
lean_dec_ref(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec_ref(v_e_1282_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(lean_object* v_scope_1289_, lean_object* v_e_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1289_, v_e_1290_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1304_, lean_object* v_e_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_, lean_object* v_a_1312_, lean_object* v_a_1313_, lean_object* v_a_1314_, lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(v_scope_1304_, v_e_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_, v_a_1312_, v_a_1313_, v_a_1314_, v_a_1315_, v_a_1316_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
lean_dec(v_a_1314_);
lean_dec_ref(v_a_1313_);
lean_dec(v_a_1312_);
lean_dec_ref(v_a_1311_);
lean_dec(v_a_1310_);
lean_dec_ref(v_a_1309_);
lean_dec(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec_ref(v_e_1305_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v___x_1332_; 
lean_inc(v___y_1326_);
lean_inc_ref(v___y_1325_);
lean_inc(v___y_1324_);
lean_inc_ref(v___y_1323_);
lean_inc(v___y_1322_);
lean_inc(v___y_1321_);
lean_inc_ref(v___y_1320_);
v___x_1332_ = lean_apply_12(v_x_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, lean_box(0));
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1347_, lean_object* v_x_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___f_1361_; lean_object* v___x_1362_; 
lean_inc(v___y_1355_);
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1353_);
lean_inc_ref(v___y_1352_);
lean_inc(v___y_1351_);
lean_inc(v___y_1350_);
lean_inc_ref(v___y_1349_);
v___f_1361_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1361_, 0, v_x_1348_);
lean_closure_set(v___f_1361_, 1, v___y_1349_);
lean_closure_set(v___f_1361_, 2, v___y_1350_);
lean_closure_set(v___f_1361_, 3, v___y_1351_);
lean_closure_set(v___f_1361_, 4, v___y_1352_);
lean_closure_set(v___f_1361_, 5, v___y_1353_);
lean_closure_set(v___f_1361_, 6, v___y_1354_);
lean_closure_set(v___f_1361_, 7, v___y_1355_);
v___x_1362_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1347_, v___f_1361_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1362_) == 0)
{
return v___x_1362_;
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1371_, lean_object* v_x_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1371_, v_x_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1386_, lean_object* v_mvarId_1387_, lean_object* v_x_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1387_, v_x_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_mvarId_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1402_, v_mvarId_1403_, v_x_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1423_, lean_object* v_scope_1424_, lean_object* v_rhs_1425_, lean_object* v_pre_1426_, lean_object* v_goal_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
if (v___x_1423_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; 
lean_dec(v_goal_1427_);
lean_dec_ref(v_pre_1426_);
lean_dec_ref(v_rhs_1425_);
lean_dec_ref(v_scope_1424_);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; 
v___x_1442_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1424_, v_rhs_1425_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1479_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1479_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1479_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
if (lean_obj_tag(v_a_1443_) == 1)
{
lean_object* v_val_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_del_object(v___x_1445_);
v_val_1447_ = lean_ctor_get(v_a_1443_, 0);
lean_inc(v_val_1447_);
lean_dec_ref_known(v_a_1443_, 1);
v___x_1448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_1449_ = l_Lean_LocalDecl_toExpr(v_val_1447_);
v___x_1450_ = lean_unsigned_to_nat(3u);
v___x_1451_ = lean_mk_empty_array_with_capacity(v___x_1450_);
v___x_1452_ = lean_array_push(v___x_1451_, v_pre_1426_);
v___x_1453_ = lean_array_push(v___x_1452_, v_rhs_1425_);
v___x_1454_ = lean_array_push(v___x_1453_, v___x_1449_);
v___x_1455_ = l_Lean_Meta_mkAppM(v___x_1448_, v___x_1454_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1465_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1427_, v_a_1456_, v___y_1436_);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1457_, 0);
lean_dec(v_unused_1466_);
v___x_1459_ = v___x_1457_;
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
else
{
lean_dec(v___x_1457_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1465_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1461_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 0, v___x_1461_);
v___x_1463_ = v___x_1459_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_goal_1427_);
v_a_1467_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1455_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1455_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_dec(v_a_1443_);
lean_dec(v_goal_1427_);
lean_dec_ref(v_pre_1426_);
lean_dec_ref(v_rhs_1425_);
v___x_1475_ = lean_box(0);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 0, v___x_1475_);
v___x_1477_ = v___x_1445_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v_goal_1427_);
lean_dec_ref(v_pre_1426_);
lean_dec_ref(v_rhs_1425_);
v_a_1480_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1442_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1442_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_1488_ = _args[0];
lean_object* v_scope_1489_ = _args[1];
lean_object* v_rhs_1490_ = _args[2];
lean_object* v_pre_1491_ = _args[3];
lean_object* v_goal_1492_ = _args[4];
lean_object* v___y_1493_ = _args[5];
lean_object* v___y_1494_ = _args[6];
lean_object* v___y_1495_ = _args[7];
lean_object* v___y_1496_ = _args[8];
lean_object* v___y_1497_ = _args[9];
lean_object* v___y_1498_ = _args[10];
lean_object* v___y_1499_ = _args[11];
lean_object* v___y_1500_ = _args[12];
lean_object* v___y_1501_ = _args[13];
lean_object* v___y_1502_ = _args[14];
lean_object* v___y_1503_ = _args[15];
lean_object* v___y_1504_ = _args[16];
_start:
{
uint8_t v___x_7757__boxed_1505_; lean_object* v_res_1506_; 
v___x_7757__boxed_1505_ = lean_unbox(v___x_1488_);
v_res_1506_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1505_, v_scope_1489_, v_rhs_1490_, v_pre_1491_, v_goal_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(lean_object* v_scope_1507_, lean_object* v_goal_1508_, lean_object* v_00_u03b1_1509_, lean_object* v_pre_1510_, lean_object* v_rhs_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_){
_start:
{
uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___y_1526_; lean_object* v___x_1527_; 
v___x_1524_ = l_Lean_Expr_isProp(v_00_u03b1_1509_);
v___x_1525_ = lean_box(v___x_1524_);
lean_inc(v_goal_1508_);
v___y_1526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1526_, 0, v___x_1525_);
lean_closure_set(v___y_1526_, 1, v_scope_1507_);
lean_closure_set(v___y_1526_, 2, v_rhs_1511_);
lean_closure_set(v___y_1526_, 3, v_pre_1510_);
lean_closure_set(v___y_1526_, 4, v_goal_1508_);
v___x_1527_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1508_, v___y_1526_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_, v_a_1522_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_1528_ = _args[0];
lean_object* v_goal_1529_ = _args[1];
lean_object* v_00_u03b1_1530_ = _args[2];
lean_object* v_pre_1531_ = _args[3];
lean_object* v_rhs_1532_ = _args[4];
lean_object* v_a_1533_ = _args[5];
lean_object* v_a_1534_ = _args[6];
lean_object* v_a_1535_ = _args[7];
lean_object* v_a_1536_ = _args[8];
lean_object* v_a_1537_ = _args[9];
lean_object* v_a_1538_ = _args[10];
lean_object* v_a_1539_ = _args[11];
lean_object* v_a_1540_ = _args[12];
lean_object* v_a_1541_ = _args[13];
lean_object* v_a_1542_ = _args[14];
lean_object* v_a_1543_ = _args[15];
lean_object* v_a_1544_ = _args[16];
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_scope_1528_, v_goal_1529_, v_00_u03b1_1530_, v_pre_1531_, v_rhs_1532_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec_ref(v_00_u03b1_1530_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1546_, lean_object* v_target_1547_, lean_object* v_goal_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1546_, v_target_1547_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1582_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1582_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1582_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
if (lean_obj_tag(v_a_1562_) == 1)
{
lean_object* v_val_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1564_);
v_val_1566_ = lean_ctor_get(v_a_1562_, 0);
lean_inc(v_val_1566_);
lean_dec_ref_known(v_a_1562_, 1);
v___x_1567_ = l_Lean_LocalDecl_toExpr(v_val_1566_);
v___x_1568_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1548_, v___x_1567_, v___y_1557_);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v___x_1568_, 0);
lean_dec(v_unused_1577_);
v___x_1570_ = v___x_1568_;
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
else
{
lean_dec(v___x_1568_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1576_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 0, v___x_1572_);
v___x_1574_ = v___x_1570_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v___x_1572_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_a_1562_);
lean_dec(v_goal_1548_);
v___x_1578_ = lean_box(0);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v___x_1578_);
v___x_1580_ = v___x_1564_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
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
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_goal_1548_);
v_a_1583_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1561_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1561_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1591_, lean_object* v_target_1592_, lean_object* v_goal_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(v_scope_1591_, v_target_1592_, v_goal_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec_ref(v_target_1592_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(lean_object* v_scope_1607_, lean_object* v_goal_1608_, lean_object* v_target_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v___f_1622_; lean_object* v___x_1623_; 
lean_inc(v_goal_1608_);
v___f_1622_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1622_, 0, v_scope_1607_);
lean_closure_set(v___f_1622_, 1, v_target_1609_);
lean_closure_set(v___f_1622_, 2, v_goal_1608_);
v___x_1623_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1608_, v___f_1622_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1624_, lean_object* v_goal_1625_, lean_object* v_target_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_1624_, v_goal_1625_, v_target_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_);
lean_dec(v_a_1637_);
lean_dec_ref(v_a_1636_);
lean_dec(v_a_1635_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec_ref(v_a_1632_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
return v_res_1639_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1646_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_1647_ = l_Lean_stringToMessageData(v___x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_1648_, lean_object* v_pre_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = l_Lean_Expr_cleanupAnnotations(v_pre_1649_);
v___x_1666_ = l_Lean_Expr_isApp(v___x_1665_);
if (v___x_1666_ == 0)
{
lean_dec_ref(v___x_1665_);
lean_dec(v_goal_1648_);
goto v___jp_1662_;
}
else
{
lean_object* v_arg_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v_arg_1667_ = lean_ctor_get(v___x_1665_, 1);
lean_inc_ref(v_arg_1667_);
v___x_1668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1665_);
v___x_1669_ = l_Lean_Expr_isApp(v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec_ref(v___x_1668_);
lean_dec_ref(v_arg_1667_);
lean_dec(v_goal_1648_);
goto v___jp_1662_;
}
else
{
lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1668_);
v___x_1671_ = l_Lean_Expr_isApp(v___x_1670_);
if (v___x_1671_ == 0)
{
lean_dec_ref(v___x_1670_);
lean_dec_ref(v_arg_1667_);
lean_dec(v_goal_1648_);
goto v___jp_1662_;
}
else
{
lean_object* v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1670_);
v___x_1673_ = l_Lean_Expr_isApp(v___x_1672_);
if (v___x_1673_ == 0)
{
lean_dec_ref(v___x_1672_);
lean_dec_ref(v_arg_1667_);
lean_dec(v_goal_1648_);
goto v___jp_1662_;
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; 
v___x_1674_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1672_);
v___x_1675_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_1676_ = l_Lean_Expr_isConstOf(v___x_1674_, v___x_1675_);
lean_dec_ref(v___x_1674_);
if (v___x_1676_ == 0)
{
lean_dec_ref(v_arg_1667_);
lean_dec(v_goal_1648_);
goto v___jp_1662_;
}
else
{
lean_object* v___x_1677_; uint8_t v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1678_ = l_Lean_Expr_isAppOf(v_arg_1667_, v___x_1677_);
lean_dec_ref(v_arg_1667_);
if (v___x_1678_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
lean_dec(v_goal_1648_);
v___x_1679_ = lean_box(0);
v___x_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v_backwardRules_1681_; lean_object* v_meetTop_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_backwardRules_1681_ = lean_ctor_get(v_a_1650_, 0);
v_meetTop_1682_ = lean_ctor_get(v_backwardRules_1681_, 8);
v___x_1683_ = lean_box(0);
lean_inc(v_goal_1648_);
lean_inc_ref(v_meetTop_1682_);
v___x_1684_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_1682_, v_goal_1648_, v___x_1683_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1711_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1711_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1711_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1692_; lean_object* v___y_1693_; 
if (lean_obj_tag(v_a_1685_) == 1)
{
lean_object* v_mvarIds_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1710_; 
v_mvarIds_1698_ = lean_ctor_get(v_a_1685_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_a_1685_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1700_ = v_a_1685_;
v_isShared_1701_ = v_isSharedCheck_1710_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_mvarIds_1698_);
lean_dec(v_a_1685_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1710_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
if (lean_obj_tag(v_mvarIds_1698_) == 1)
{
lean_object* v_tail_1702_; 
v_tail_1702_ = lean_ctor_get(v_mvarIds_1698_, 1);
if (lean_obj_tag(v_tail_1702_) == 0)
{
lean_object* v_head_1703_; lean_object* v___x_1705_; 
lean_dec(v_goal_1648_);
v_head_1703_ = lean_ctor_get(v_mvarIds_1698_, 0);
lean_inc(v_head_1703_);
lean_dec_ref_known(v_mvarIds_1698_, 2);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v_head_1703_);
v___x_1705_ = v___x_1700_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_head_1703_);
v___x_1705_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1707_; 
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1705_);
v___x_1707_ = v___x_1687_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1698_, 2);
lean_del_object(v___x_1700_);
lean_del_object(v___x_1687_);
v___y_1690_ = v_a_1657_;
v___y_1691_ = v_a_1658_;
v___y_1692_ = v_a_1659_;
v___y_1693_ = v_a_1660_;
goto v___jp_1689_;
}
}
else
{
lean_del_object(v___x_1700_);
lean_dec(v_mvarIds_1698_);
lean_del_object(v___x_1687_);
v___y_1690_ = v_a_1657_;
v___y_1691_ = v_a_1658_;
v___y_1692_ = v_a_1659_;
v___y_1693_ = v_a_1660_;
goto v___jp_1689_;
}
}
}
else
{
lean_del_object(v___x_1687_);
lean_dec(v_a_1685_);
v___y_1690_ = v_a_1657_;
v___y_1691_ = v_a_1658_;
v___y_1692_ = v_a_1659_;
v___y_1693_ = v_a_1660_;
goto v___jp_1689_;
}
v___jp_1689_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1694_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_goal_1648_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1696_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1697_;
}
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec(v_goal_1648_);
v_a_1712_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1684_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1684_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
}
}
}
}
v___jp_1662_:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_1720_, lean_object* v_pre_1721_, lean_object* v_a_1722_, lean_object* v_a_1723_, lean_object* v_a_1724_, lean_object* v_a_1725_, lean_object* v_a_1726_, lean_object* v_a_1727_, lean_object* v_a_1728_, lean_object* v_a_1729_, lean_object* v_a_1730_, lean_object* v_a_1731_, lean_object* v_a_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_1720_, v_pre_1721_, v_a_1722_, v_a_1723_, v_a_1724_, v_a_1725_, v_a_1726_, v_a_1727_, v_a_1728_, v_a_1729_, v_a_1730_, v_a_1731_, v_a_1732_);
lean_dec(v_a_1732_);
lean_dec_ref(v_a_1731_);
lean_dec(v_a_1730_);
lean_dec_ref(v_a_1729_);
lean_dec(v_a_1728_);
lean_dec_ref(v_a_1727_);
lean_dec(v_a_1726_);
lean_dec_ref(v_a_1725_);
lean_dec(v_a_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_a_1722_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_1742_, lean_object* v_pre_1743_, lean_object* v_a_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_, lean_object* v_a_1750_, lean_object* v_a_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_){
_start:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; 
v___x_1759_ = l_Lean_Expr_cleanupAnnotations(v_pre_1743_);
v___x_1760_ = l_Lean_Expr_isApp(v___x_1759_);
if (v___x_1760_ == 0)
{
lean_dec_ref(v___x_1759_);
lean_dec(v_goal_1742_);
goto v___jp_1756_;
}
else
{
lean_object* v_arg_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_arg_1761_ = lean_ctor_get(v___x_1759_, 1);
lean_inc_ref(v_arg_1761_);
v___x_1762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1759_);
v___x_1763_ = l_Lean_Expr_isApp(v___x_1762_);
if (v___x_1763_ == 0)
{
lean_dec_ref(v___x_1762_);
lean_dec_ref(v_arg_1761_);
lean_dec(v_goal_1742_);
goto v___jp_1756_;
}
else
{
lean_object* v___x_1764_; uint8_t v___x_1765_; 
v___x_1764_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1762_);
v___x_1765_ = l_Lean_Expr_isApp(v___x_1764_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v___x_1764_);
lean_dec_ref(v_arg_1761_);
lean_dec(v_goal_1742_);
goto v___jp_1756_;
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1766_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1764_);
v___x_1767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_1768_ = l_Lean_Expr_isConstOf(v___x_1766_, v___x_1767_);
lean_dec_ref(v___x_1766_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v_arg_1761_);
lean_dec(v_goal_1742_);
goto v___jp_1756_;
}
else
{
uint8_t v___x_1769_; 
v___x_1769_ = l_Lean_Expr_isTrue(v_arg_1761_);
if (v___x_1769_ == 0)
{
lean_object* v_backwardRules_1770_; lean_object* v_ofPropPreIntro_1771_; lean_object* v___x_1772_; 
v_backwardRules_1770_ = lean_ctor_get(v_a_1744_, 0);
v_ofPropPreIntro_1771_ = lean_ctor_get(v_backwardRules_1770_, 3);
lean_inc_ref(v_ofPropPreIntro_1771_);
v___x_1772_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_ofPropPreIntro_1771_, v_goal_1742_, v_a_1744_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_, v_a_1750_, v_a_1751_, v_a_1752_, v_a_1753_, v_a_1754_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1781_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1777_, 0, v_a_1773_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1772_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1772_);
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
lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec(v_goal_1742_);
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1790_);
return v___x_1791_;
}
}
}
}
}
v___jp_1756_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_1792_, lean_object* v_pre_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_1792_, v_pre_1793_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
lean_dec(v_a_1804_);
lean_dec_ref(v_a_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec(v_a_1798_);
lean_dec_ref(v_a_1797_);
lean_dec(v_a_1796_);
lean_dec(v_a_1795_);
lean_dec_ref(v_a_1794_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(lean_object* v_goal_1807_, lean_object* v_00_u03b1_1808_, lean_object* v_pre_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = l_Lean_Expr_isProp(v_00_u03b1_1808_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
lean_dec(v_goal_1807_);
v___x_1823_ = lean_box(0);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
else
{
lean_object* v___x_1825_; uint8_t v___x_1826_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1826_ = l_Lean_Expr_isAppOf(v_pre_1809_, v___x_1825_);
if (v___x_1826_ == 0)
{
lean_object* v_backwardRules_1827_; lean_object* v_propPreIntro_1828_; lean_object* v___x_1829_; 
v_backwardRules_1827_ = lean_ctor_get(v_a_1810_, 0);
v_propPreIntro_1828_ = lean_ctor_get(v_backwardRules_1827_, 2);
lean_inc_ref(v_propPreIntro_1828_);
v___x_1829_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_propPreIntro_1828_, v_goal_1807_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1838_; 
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1834_, 0, v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
v_a_1839_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1829_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1829_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
else
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
lean_dec(v_goal_1807_);
v___x_1847_ = lean_box(0);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_1849_, lean_object* v_00_u03b1_1850_, lean_object* v_pre_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_1849_, v_00_u03b1_1850_, v_pre_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
lean_dec(v_a_1862_);
lean_dec_ref(v_a_1861_);
lean_dec(v_a_1860_);
lean_dec_ref(v_a_1859_);
lean_dec(v_a_1858_);
lean_dec_ref(v_a_1857_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec_ref(v_pre_1851_);
lean_dec_ref(v_00_u03b1_1850_);
return v_res_1864_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1866_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0));
v___x_1867_ = l_Lean_stringToMessageData(v___x_1866_);
return v___x_1867_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = 0;
v___x_1874_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3));
v___x_1875_ = l_Lean_MessageData_ofConstName(v___x_1874_, v___x_1873_);
return v___x_1875_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4);
v___x_1877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6));
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7);
v___x_1883_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(lean_object* v_goal_1885_, lean_object* v_pre_1886_, lean_object* v_target_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___x_1938_; 
lean_inc_ref(v_pre_1886_);
v___x_1938_ = l_Lean_Expr_isTrue(v_pre_1886_);
if (v___x_1938_ == 0)
{
v___y_1901_ = v_a_1893_;
v___y_1902_ = v_a_1894_;
v___y_1903_ = v_a_1895_;
v___y_1904_ = v_a_1896_;
v___y_1905_ = v_a_1897_;
v___y_1906_ = v_a_1898_;
goto v___jp_1900_;
}
else
{
lean_object* v_backwardRules_1939_; lean_object* v_truePreIntro_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec_ref(v_pre_1886_);
v_backwardRules_1939_ = lean_ctor_get(v_a_1888_, 0);
v_truePreIntro_1940_ = lean_ctor_get(v_backwardRules_1939_, 4);
v___x_1941_ = lean_box(0);
lean_inc_ref(v_truePreIntro_1940_);
v___x_1942_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_1940_, v_goal_1885_, v___x_1941_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1978_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1978_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1978_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; 
if (lean_obj_tag(v_a_1943_) == 1)
{
lean_object* v_mvarIds_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1977_; 
v_mvarIds_1966_ = lean_ctor_get(v_a_1943_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1943_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1968_ = v_a_1943_;
v_isShared_1969_ = v_isSharedCheck_1977_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_mvarIds_1966_);
lean_dec(v_a_1943_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1977_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
if (lean_obj_tag(v_mvarIds_1966_) == 1)
{
lean_object* v_tail_1970_; 
v_tail_1970_ = lean_ctor_get(v_mvarIds_1966_, 1);
if (lean_obj_tag(v_tail_1970_) == 0)
{
lean_object* v___x_1972_; 
lean_dec_ref(v_target_1887_);
if (v_isShared_1969_ == 0)
{
v___x_1972_ = v___x_1968_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_mvarIds_1966_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1972_);
v___x_1974_ = v___x_1945_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1966_, 2);
lean_del_object(v___x_1968_);
lean_del_object(v___x_1945_);
v___y_1948_ = v_a_1893_;
v___y_1949_ = v_a_1894_;
v___y_1950_ = v_a_1895_;
v___y_1951_ = v_a_1896_;
v___y_1952_ = v_a_1897_;
v___y_1953_ = v_a_1898_;
goto v___jp_1947_;
}
}
else
{
lean_del_object(v___x_1968_);
lean_dec(v_mvarIds_1966_);
lean_del_object(v___x_1945_);
v___y_1948_ = v_a_1893_;
v___y_1949_ = v_a_1894_;
v___y_1950_ = v_a_1895_;
v___y_1951_ = v_a_1896_;
v___y_1952_ = v_a_1897_;
v___y_1953_ = v_a_1898_;
goto v___jp_1947_;
}
}
}
else
{
lean_del_object(v___x_1945_);
lean_dec(v_a_1943_);
v___y_1948_ = v_a_1893_;
v___y_1949_ = v_a_1894_;
v___y_1950_ = v_a_1895_;
v___y_1951_ = v_a_1896_;
v___y_1952_ = v_a_1897_;
v___y_1953_ = v_a_1898_;
goto v___jp_1947_;
}
v___jp_1947_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_a_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1965_; 
v___x_1954_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8);
v___x_1955_ = l_Lean_indentExpr(v_target_1887_);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1956_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
v_isSharedCheck_1965_ = !lean_is_exclusive(v___x_1957_);
if (v_isSharedCheck_1965_ == 0)
{
v___x_1960_ = v___x_1957_;
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_a_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1965_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1963_; 
if (v_isShared_1961_ == 0)
{
v___x_1963_ = v___x_1960_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_a_1958_);
v___x_1963_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
return v___x_1963_;
}
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v_target_1887_);
v_a_1979_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1942_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1942_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
v___jp_1900_:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(v_goal_1885_, v_target_1887_, v_pre_1886_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1929_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1910_ = v___x_1907_;
v_isShared_1911_ = v_isSharedCheck_1929_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1907_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1929_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
if (lean_obj_tag(v_a_1908_) == 1)
{
lean_object* v_val_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1924_; 
v_val_1912_ = lean_ctor_get(v_a_1908_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_a_1908_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1914_ = v_a_1908_;
v_isShared_1915_ = v_isSharedCheck_1924_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_val_1912_);
lean_dec(v_a_1908_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1924_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_val_1912_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v___x_1917_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
lean_object* v___x_1921_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1919_);
v___x_1921_ = v___x_1910_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1919_);
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
lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_dec(v_a_1908_);
v___x_1925_ = lean_box(0);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 0, v___x_1925_);
v___x_1927_ = v___x_1910_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
v_a_1930_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1907_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1907_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_1987_, lean_object* v_pre_1988_, lean_object* v_target_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_1987_, v_pre_1988_, v_target_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_, v_a_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_a_1999_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object* v_scope_2003_, lean_object* v_goal_2004_, lean_object* v_00_u03b1_2005_, lean_object* v_pre_2006_, lean_object* v_target_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_g_2021_; lean_object* v_g_2028_; lean_object* v_h_2029_; lean_object* v___x_2047_; 
lean_inc_ref(v_pre_2006_);
lean_inc(v_goal_2004_);
v___x_2047_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_2004_, v_pre_2006_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
if (lean_obj_tag(v_a_2048_) == 1)
{
lean_object* v_val_2049_; 
lean_dec_ref(v_target_2007_);
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
v_val_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref_known(v_a_2048_, 1);
v_g_2021_ = v_val_2049_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2050_; 
lean_dec(v_a_2048_);
lean_inc_ref(v_pre_2006_);
lean_inc(v_goal_2004_);
v___x_2050_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_2004_, v_pre_2006_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
if (lean_obj_tag(v_a_2051_) == 1)
{
lean_object* v_val_2052_; lean_object* v_fst_2053_; lean_object* v_snd_2054_; 
lean_dec_ref(v_target_2007_);
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
v_val_2052_ = lean_ctor_get(v_a_2051_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v_a_2051_, 1);
v_fst_2053_ = lean_ctor_get(v_val_2052_, 0);
lean_inc(v_fst_2053_);
v_snd_2054_ = lean_ctor_get(v_val_2052_, 1);
lean_inc(v_snd_2054_);
lean_dec(v_val_2052_);
v_g_2028_ = v_fst_2053_;
v_h_2029_ = v_snd_2054_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2055_; 
lean_dec(v_a_2051_);
lean_inc(v_goal_2004_);
v___x_2055_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_2004_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
if (lean_obj_tag(v_a_2056_) == 1)
{
lean_object* v_val_2057_; 
lean_dec_ref(v_target_2007_);
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
v_val_2057_ = lean_ctor_get(v_a_2056_, 0);
lean_inc(v_val_2057_);
lean_dec_ref_known(v_a_2056_, 1);
v_g_2021_ = v_val_2057_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_a_2056_);
lean_inc_ref(v_pre_2006_);
lean_inc(v_goal_2004_);
v___x_2058_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2004_, v_pre_2006_, v_target_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2096_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2061_ = v___x_2058_;
v_isShared_2062_ = v_isSharedCheck_2096_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2058_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2096_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
if (lean_obj_tag(v_a_2059_) == 1)
{
lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
v_val_2063_ = lean_ctor_get(v_a_2059_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_a_2059_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2065_ = v_a_2059_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v_a_2059_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2067_, 0, v_scope_2003_);
lean_ctor_set(v___x_2067_, 1, v_val_2063_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2067_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2069_);
v___x_2071_ = v___x_2061_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v___x_2075_; 
lean_del_object(v___x_2061_);
lean_dec(v_a_2059_);
v___x_2075_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_2004_, v_00_u03b1_2005_, v_pre_2006_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_, v_a_2016_, v_a_2017_, v_a_2018_);
lean_dec_ref(v_pre_2006_);
if (lean_obj_tag(v___x_2075_) == 0)
{
lean_object* v_a_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2087_; 
v_a_2076_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2078_ = v___x_2075_;
v_isShared_2079_ = v_isSharedCheck_2087_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_a_2076_);
lean_dec(v___x_2075_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2087_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
if (lean_obj_tag(v_a_2076_) == 1)
{
lean_object* v_val_2080_; lean_object* v_fst_2081_; lean_object* v_snd_2082_; 
lean_del_object(v___x_2078_);
v_val_2080_ = lean_ctor_get(v_a_2076_, 0);
lean_inc(v_val_2080_);
lean_dec_ref_known(v_a_2076_, 1);
v_fst_2081_ = lean_ctor_get(v_val_2080_, 0);
lean_inc(v_fst_2081_);
v_snd_2082_ = lean_ctor_get(v_val_2080_, 1);
lean_inc(v_snd_2082_);
lean_dec(v_val_2080_);
v_g_2028_ = v_fst_2081_;
v_h_2029_ = v_snd_2082_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec(v_a_2076_);
lean_dec_ref(v_scope_2003_);
v___x_2083_ = lean_box(0);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2083_);
v___x_2085_ = v___x_2078_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
else
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
lean_dec_ref(v_scope_2003_);
v_a_2088_ = lean_ctor_get(v___x_2075_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2090_ = v___x_2075_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2075_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2088_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
lean_dec_ref(v_scope_2003_);
v_a_2097_ = lean_ctor_get(v___x_2058_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2058_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2058_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2058_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_target_2007_);
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
lean_dec_ref(v_scope_2003_);
v_a_2105_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2055_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2055_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_target_2007_);
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
lean_dec_ref(v_scope_2003_);
v_a_2113_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2050_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2050_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_target_2007_);
lean_dec_ref(v_pre_2006_);
lean_dec(v_goal_2004_);
lean_dec_ref(v_scope_2003_);
v_a_2121_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2047_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2047_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
v___jp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_g_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_scope_2003_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
return v___x_2026_;
}
v___jp_2027_:
{
lean_object* v_specs_2030_; lean_object* v_jps_2031_; lean_object* v_nextDeclIdx_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2045_; 
v_specs_2030_ = lean_ctor_get(v_scope_2003_, 0);
v_jps_2031_ = lean_ctor_get(v_scope_2003_, 1);
v_nextDeclIdx_2032_ = lean_ctor_get(v_scope_2003_, 3);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_scope_2003_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v_scope_2003_, 2);
lean_dec(v_unused_2046_);
v___x_2034_ = v_scope_2003_;
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_nextDeclIdx_2032_);
lean_inc(v_jps_2031_);
lean_inc(v_specs_2030_);
lean_dec(v_scope_2003_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_h_2029_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 2, v___x_2036_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_specs_2030_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_jps_2031_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_nextDeclIdx_2032_);
v___x_2038_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2039_ = lean_box(0);
v___x_2040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_g_2028_);
lean_ctor_set(v___x_2040_, 1, v___x_2039_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2038_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2129_ = _args[0];
lean_object* v_goal_2130_ = _args[1];
lean_object* v_00_u03b1_2131_ = _args[2];
lean_object* v_pre_2132_ = _args[3];
lean_object* v_target_2133_ = _args[4];
lean_object* v_a_2134_ = _args[5];
lean_object* v_a_2135_ = _args[6];
lean_object* v_a_2136_ = _args[7];
lean_object* v_a_2137_ = _args[8];
lean_object* v_a_2138_ = _args[9];
lean_object* v_a_2139_ = _args[10];
lean_object* v_a_2140_ = _args[11];
lean_object* v_a_2141_ = _args[12];
lean_object* v_a_2142_ = _args[13];
lean_object* v_a_2143_ = _args[14];
lean_object* v_a_2144_ = _args[15];
lean_object* v_a_2145_ = _args[16];
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_2129_, v_goal_2130_, v_00_u03b1_2131_, v_pre_2132_, v_target_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
lean_dec(v_a_2140_);
lean_dec_ref(v_a_2139_);
lean_dec(v_a_2138_);
lean_dec_ref(v_a_2137_);
lean_dec(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_00_u03b1_2131_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2147_, lean_object* v_a_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___y_2157_; lean_object* v___x_2160_; uint8_t v_debug_2161_; 
v___x_2160_ = lean_st_ref_get(v___y_2150_);
v_debug_2161_ = lean_ctor_get_uint8(v___x_2160_, sizeof(void*)*11);
lean_dec(v___x_2160_);
if (v_debug_2161_ == 0)
{
v___y_2157_ = v___y_2150_;
goto v___jp_2156_;
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2147_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2162_) == 0)
{
lean_object* v___x_2163_; 
lean_dec_ref_known(v___x_2162_, 1);
v___x_2163_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2163_) == 0)
{
lean_dec_ref_known(v___x_2163_, 1);
v___y_2157_ = v___y_2150_;
goto v___jp_2156_;
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_f_2147_);
v_a_2164_ = lean_ctor_get(v___x_2163_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2163_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2163_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2163_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v_a_2148_);
lean_dec_ref(v_f_2147_);
v_a_2172_ = lean_ctor_get(v___x_2162_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
v___jp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = l_Lean_Expr_app___override(v_f_2147_, v_a_2148_);
v___x_2159_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2158_, v___y_2157_);
return v___x_2159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2180_, lean_object* v_a_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2180_, v_a_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object* v_args_2190_, lean_object* v_endIdx_2191_, lean_object* v_b_2192_, lean_object* v_i_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_nat_dec_le(v_endIdx_2191_, v_i_2193_);
if (v___x_2206_ == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = l_Lean_instInhabitedExpr;
v___x_2208_ = lean_array_get_borrowed(v___x_2207_, v_args_2190_, v_i_2193_);
lean_inc(v___x_2208_);
v___x_2209_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2192_, v___x_2208_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = lean_unsigned_to_nat(1u);
v___x_2212_ = lean_nat_add(v_i_2193_, v___x_2211_);
lean_dec(v_i_2193_);
v_b_2192_ = v_a_2210_;
v_i_2193_ = v___x_2212_;
goto _start;
}
else
{
lean_dec(v_i_2193_);
return v___x_2209_;
}
}
else
{
lean_object* v___x_2214_; 
lean_dec(v_i_2193_);
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v_b_2192_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object* v_args_2215_, lean_object* v_endIdx_2216_, lean_object* v_b_2217_, lean_object* v_i_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2215_, v_endIdx_2216_, v_b_2217_, v_i_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec(v_endIdx_2216_);
lean_dec_ref(v_args_2215_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object* v_f_2232_, lean_object* v_args_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_array_get_size(v_args_2233_);
v___x_2248_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2233_, v___x_2247_, v_f_2232_, v___x_2246_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object* v_f_2249_, lean_object* v_args_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_2249_, v_args_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_args_2250_);
return v_res_2263_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0(void){
_start:
{
lean_object* v___x_2264_; lean_object* v_dummy_2265_; 
v___x_2264_ = lean_box(0);
v_dummy_2265_ = l_Lean_Expr_sort___override(v___x_2264_);
return v_dummy_2265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_2266_, lean_object* v_info_2267_, lean_object* v_prog_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_head_2281_; lean_object* v_args_2282_; lean_object* v_excessArgs_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_head_2281_ = lean_ctor_get(v_info_2267_, 0);
lean_inc_ref(v_head_2281_);
v_args_2282_ = lean_ctor_get(v_info_2267_, 1);
lean_inc_ref(v_args_2282_);
v_excessArgs_2283_ = lean_ctor_get(v_info_2267_, 2);
lean_inc_ref(v_excessArgs_2283_);
lean_dec_ref(v_info_2267_);
v___x_2284_ = lean_unsigned_to_nat(7u);
v___x_2285_ = lean_array_set(v_args_2282_, v___x_2284_, v_prog_2268_);
v___x_2286_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2281_, v___x_2285_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v___x_2285_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2287_, v_excessArgs_2283_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v_excessArgs_2283_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref_known(v___x_2288_, 1);
lean_inc(v_goal_2266_);
v___x_2290_ = l_Lean_MVarId_getType(v_goal_2266_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v_dummy_2292_; lean_object* v_nargs_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc_n(v_a_2291_, 2);
lean_dec_ref_known(v___x_2290_, 1);
v_dummy_2292_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0);
v_nargs_2293_ = l_Lean_Expr_getAppNumArgs(v_a_2291_);
lean_inc(v_nargs_2293_);
v___x_2294_ = lean_mk_array(v_nargs_2293_, v_dummy_2292_);
v___x_2295_ = lean_unsigned_to_nat(1u);
v___x_2296_ = lean_nat_sub(v_nargs_2293_, v___x_2295_);
lean_dec(v_nargs_2293_);
v___x_2297_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2291_, v___x_2294_, v___x_2296_);
v___x_2298_ = l_Lean_Expr_getAppFn(v_a_2291_);
lean_dec(v_a_2291_);
v___x_2299_ = lean_array_get_size(v___x_2297_);
v___x_2300_ = lean_nat_sub(v___x_2299_, v___x_2295_);
v___x_2301_ = lean_array_set(v___x_2297_, v___x_2300_, v_a_2289_);
lean_dec(v___x_2300_);
v___x_2302_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2298_, v___x_2301_, v_a_2269_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v___x_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2266_, v_a_2303_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2304_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_goal_2266_);
v_a_2305_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2302_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2302_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_dec(v_a_2289_);
lean_dec(v_goal_2266_);
v_a_2313_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2290_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2290_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
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
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec(v_goal_2266_);
v_a_2321_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_2288_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2288_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2336_; 
lean_dec_ref(v_excessArgs_2283_);
lean_dec(v_goal_2266_);
v_a_2329_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2336_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2336_ == 0)
{
v___x_2331_ = v___x_2286_;
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_a_2329_);
lean_dec(v___x_2286_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2336_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2334_; 
if (v_isShared_2332_ == 0)
{
v___x_2334_ = v___x_2331_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_a_2329_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2337_, lean_object* v_info_2338_, lean_object* v_prog_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2337_, v_info_2338_, v_prog_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_a_2346_);
lean_dec_ref(v_a_2345_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(lean_object* v_f_2353_, lean_object* v_a_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2353_, v_a_2354_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2368_, lean_object* v_a_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(v_f_2368_, v_a_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec(v___y_2371_);
lean_dec_ref(v___y_2370_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(lean_object* v_goal_2383_, lean_object* v_info_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_2384_);
if (lean_obj_tag(v___x_2397_) == 10)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = l_Lean_Expr_consumeMData(v___x_2397_);
lean_dec_ref_known(v___x_2397_, 2);
v___x_2399_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2383_, v_info_2384_, v___x_2398_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v_a_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2399_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2399_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
else
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v___x_2397_);
lean_dec_ref(v_info_2384_);
lean_dec(v_goal_2383_);
v___x_2417_ = lean_box(0);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
return v___x_2418_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_2419_, lean_object* v_info_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_, lean_object* v_a_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_2419_, v_info_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_, v_a_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_, v_a_2431_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
lean_dec(v_a_2425_);
lean_dec_ref(v_a_2424_);
lean_dec(v_a_2423_);
lean_dec(v_a_2422_);
lean_dec_ref(v_a_2421_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2434_, lean_object* v_start_2435_, lean_object* v_b_2436_, lean_object* v_i_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
uint8_t v___x_2445_; 
v___x_2445_ = lean_nat_dec_le(v_i_2437_, v_start_2435_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; lean_object* v_i_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2446_ = lean_unsigned_to_nat(1u);
v_i_2447_ = lean_nat_sub(v_i_2437_, v___x_2446_);
lean_dec(v_i_2437_);
v___x_2448_ = l_Lean_instInhabitedExpr;
v___x_2449_ = lean_array_get_borrowed(v___x_2448_, v_revArgs_2434_, v_i_2447_);
lean_inc(v___x_2449_);
v___x_2450_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2436_, v___x_2449_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref_known(v___x_2450_, 1);
v_b_2436_ = v_a_2451_;
v_i_2437_ = v_i_2447_;
goto _start;
}
else
{
lean_dec(v_i_2447_);
return v___x_2450_;
}
}
else
{
lean_object* v___x_2453_; 
lean_dec(v_i_2437_);
v___x_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_b_2436_);
return v___x_2453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2454_, lean_object* v_start_2455_, lean_object* v_b_2456_, lean_object* v_i_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2454_, v_start_2455_, v_b_2456_, v_i_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v_start_2455_);
lean_dec_ref(v_revArgs_2454_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2466_, lean_object* v_revArgs_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_unsigned_to_nat(0u);
v___x_2481_ = lean_array_get_size(v_revArgs_2467_);
v___x_2482_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2467_, v___x_2480_, v_f_2466_, v___x_2481_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_2483_, lean_object* v_revArgs_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_f_2483_, v_revArgs_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec_ref(v_revArgs_2484_);
return v_res_2497_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0));
v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2));
v___x_2503_ = l_Lean_stringToMessageData(v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object* v_goal_2504_, lean_object* v_info_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_, lean_object* v_a_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_){
_start:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2518_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_2505_);
v___x_2519_ = l_Lean_Expr_getAppFn(v___x_2518_);
if (lean_obj_tag(v___x_2519_) == 8)
{
lean_object* v_declName_2520_; lean_object* v_type_2521_; lean_object* v_value_2522_; lean_object* v_body_2523_; uint8_t v_nondep_2524_; lean_object* v___x_2525_; 
v_declName_2520_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_n(v_declName_2520_, 2);
v_type_2521_ = lean_ctor_get(v___x_2519_, 1);
lean_inc_ref(v_type_2521_);
v_value_2522_ = lean_ctor_get(v___x_2519_, 2);
lean_inc_ref(v_value_2522_);
v_body_2523_ = lean_ctor_get(v___x_2519_, 3);
lean_inc_ref(v_body_2523_);
v_nondep_2524_ = lean_ctor_get_uint8(v___x_2519_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_2519_, 4);
v___x_2525_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_2520_, v_value_2522_, v_a_2506_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v_appArgs_2528_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; uint8_t v___x_2582_; 
lean_dec_ref_known(v___x_2525_, 1);
v___x_2526_ = l_Lean_Expr_getAppNumArgs(v___x_2518_);
v___x_2527_ = lean_mk_empty_array_with_capacity(v___x_2526_);
lean_dec(v___x_2526_);
v_appArgs_2528_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2518_, v___x_2527_);
v___x_2582_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_2522_);
if (v___x_2582_ == 0)
{
lean_object* v_options_2583_; lean_object* v_inheritedTraceOptions_2584_; uint8_t v_hasTrace_2585_; uint8_t v___x_2586_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; 
v_options_2583_ = lean_ctor_get(v_a_2515_, 2);
v_inheritedTraceOptions_2584_ = lean_ctor_get(v_a_2515_, 13);
v_hasTrace_2585_ = lean_ctor_get_uint8(v_options_2583_, sizeof(void*)*1);
v___x_2586_ = 1;
if (v_hasTrace_2585_ == 0)
{
v___y_2588_ = v_a_2506_;
v___y_2589_ = v_a_2507_;
v___y_2590_ = v_a_2508_;
v___y_2591_ = v_a_2509_;
v___y_2592_ = v_a_2510_;
v___y_2593_ = v_a_2511_;
v___y_2594_ = v_a_2512_;
v___y_2595_ = v_a_2513_;
v___y_2596_ = v_a_2514_;
v___y_2597_ = v_a_2515_;
v___y_2598_ = v_a_2516_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v___x_2697_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2698_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2584_, v_options_2583_, v___x_2698_);
if (v___x_2699_ == 0)
{
v___y_2588_ = v_a_2506_;
v___y_2589_ = v_a_2507_;
v___y_2590_ = v_a_2508_;
v___y_2591_ = v_a_2509_;
v___y_2592_ = v_a_2510_;
v___y_2593_ = v_a_2511_;
v___y_2594_ = v_a_2512_;
v___y_2595_ = v_a_2513_;
v___y_2596_ = v_a_2514_;
v___y_2597_ = v_a_2515_;
v___y_2598_ = v_a_2516_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2700_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_2520_);
v___x_2701_ = l_Lean_MessageData_ofName(v_declName_2520_);
v___x_2702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2700_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2697_, v___x_2702_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_dec_ref_known(v___x_2703_, 1);
v___y_2588_ = v_a_2506_;
v___y_2589_ = v_a_2507_;
v___y_2590_ = v_a_2508_;
v___y_2591_ = v_a_2509_;
v___y_2592_ = v_a_2510_;
v___y_2593_ = v_a_2511_;
v___y_2594_ = v_a_2512_;
v___y_2595_ = v_a_2513_;
v___y_2596_ = v_a_2514_;
v___y_2597_ = v_a_2515_;
v___y_2598_ = v_a_2516_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2711_; 
lean_dec_ref(v_appArgs_2528_);
lean_dec_ref(v_body_2523_);
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2711_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v___x_2709_; 
if (v_isShared_2707_ == 0)
{
v___x_2709_ = v___x_2706_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_a_2704_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
}
v___jp_2587_:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_body_2523_, v_appArgs_2528_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v_appArgs_2528_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v_head_2601_; lean_object* v_args_2602_; lean_object* v_excessArgs_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_a_2600_);
lean_dec_ref_known(v___x_2599_, 1);
v_head_2601_ = lean_ctor_get(v_info_2505_, 0);
lean_inc_ref(v_head_2601_);
v_args_2602_ = lean_ctor_get(v_info_2505_, 1);
lean_inc_ref(v_args_2602_);
v_excessArgs_2603_ = lean_ctor_get(v_info_2505_, 2);
lean_inc_ref(v_excessArgs_2603_);
lean_dec_ref(v_info_2505_);
v___x_2604_ = lean_unsigned_to_nat(7u);
v___x_2605_ = lean_array_set(v_args_2602_, v___x_2604_, v_a_2600_);
v___x_2606_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2601_, v___x_2605_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v___x_2605_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2607_, v_excessArgs_2603_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v_excessArgs_2603_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
lean_inc(v_goal_2504_);
v___x_2610_ = l_Lean_MVarId_getType(v_goal_2504_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v_dummy_2612_; lean_object* v_nargs_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc_n(v_a_2611_, 2);
lean_dec_ref_known(v___x_2610_, 1);
v_dummy_2612_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___closed__0);
v_nargs_2613_ = l_Lean_Expr_getAppNumArgs(v_a_2611_);
lean_inc(v_nargs_2613_);
v___x_2614_ = lean_mk_array(v_nargs_2613_, v_dummy_2612_);
v___x_2615_ = lean_unsigned_to_nat(1u);
v___x_2616_ = lean_nat_sub(v_nargs_2613_, v___x_2615_);
lean_dec(v_nargs_2613_);
v___x_2617_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2611_, v___x_2614_, v___x_2616_);
v___x_2618_ = l_Lean_Expr_getAppFn(v_a_2611_);
lean_dec(v_a_2611_);
v___x_2619_ = lean_array_get_size(v___x_2617_);
v___x_2620_ = lean_nat_sub(v___x_2619_, v___x_2615_);
v___x_2621_ = lean_array_set(v___x_2617_, v___x_2620_, v_a_2609_);
lean_dec(v___x_2620_);
v___x_2622_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2618_, v___x_2621_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec_ref(v___x_2621_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___x_2622_, 1);
v___x_2624_ = l_Lean_Expr_letE___override(v_declName_2520_, v_type_2521_, v_value_2522_, v_a_2623_, v_nondep_2524_);
v___x_2625_ = l_Lean_MVarId_replaceTargetDefEqFast(v_goal_2504_, v___x_2624_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2628_ = l_Lean_Meta_Sym_intros(v_a_2626_, v___x_2627_, v___x_2586_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
if (lean_obj_tag(v___x_2628_) == 0)
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2640_; 
v_a_2629_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2631_ = v___x_2628_;
v_isShared_2632_ = v_isSharedCheck_2640_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2628_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2640_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
if (lean_obj_tag(v_a_2629_) == 1)
{
lean_object* v_mvarId_2633_; lean_object* v___x_2634_; lean_object* v___x_2636_; 
v_mvarId_2633_ = lean_ctor_get(v_a_2629_, 1);
lean_inc(v_mvarId_2633_);
lean_dec_ref_known(v_a_2629_, 2);
v___x_2634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_mvarId_2633_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 0, v___x_2634_);
v___x_2636_ = v___x_2631_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
else
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
lean_del_object(v___x_2631_);
lean_dec(v_a_2629_);
v___x_2638_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1);
v___x_2639_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2638_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2639_;
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_a_2641_ = lean_ctor_get(v___x_2628_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2628_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2628_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2628_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
v_a_2649_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2625_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2625_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec(v_goal_2504_);
v_a_2657_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2622_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2622_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
lean_dec(v_a_2609_);
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec(v_goal_2504_);
v_a_2665_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2610_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2610_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec(v_goal_2504_);
v_a_2673_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2608_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2608_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v_excessArgs_2603_);
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec(v_goal_2504_);
v_a_2681_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2606_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2606_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v_a_2689_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2599_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2599_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
else
{
lean_object* v_options_2712_; uint8_t v_hasTrace_2713_; 
lean_dec_ref(v_type_2521_);
v_options_2712_ = lean_ctor_get(v_a_2515_, 2);
v_hasTrace_2713_ = lean_ctor_get_uint8(v_options_2712_, sizeof(void*)*1);
if (v_hasTrace_2713_ == 0)
{
lean_dec(v_declName_2520_);
v___y_2530_ = v_a_2506_;
v___y_2531_ = v_a_2507_;
v___y_2532_ = v_a_2508_;
v___y_2533_ = v_a_2509_;
v___y_2534_ = v_a_2510_;
v___y_2535_ = v_a_2511_;
v___y_2536_ = v_a_2512_;
v___y_2537_ = v_a_2513_;
v___y_2538_ = v_a_2514_;
v___y_2539_ = v_a_2515_;
v___y_2540_ = v_a_2516_;
goto v___jp_2529_;
}
else
{
lean_object* v_inheritedTraceOptions_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; 
v_inheritedTraceOptions_2714_ = lean_ctor_get(v_a_2515_, 13);
v___x_2715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2714_, v_options_2712_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_dec(v_declName_2520_);
v___y_2530_ = v_a_2506_;
v___y_2531_ = v_a_2507_;
v___y_2532_ = v_a_2508_;
v___y_2533_ = v_a_2509_;
v___y_2534_ = v_a_2510_;
v___y_2535_ = v_a_2511_;
v___y_2536_ = v_a_2512_;
v___y_2537_ = v_a_2513_;
v___y_2538_ = v_a_2514_;
v___y_2539_ = v_a_2515_;
v___y_2540_ = v_a_2516_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2718_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_2719_ = l_Lean_MessageData_ofName(v_declName_2520_);
v___x_2720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2718_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v___x_2721_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2715_, v___x_2720_, v_a_2513_, v_a_2514_, v_a_2515_, v_a_2516_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_dec_ref_known(v___x_2721_, 1);
v___y_2530_ = v_a_2506_;
v___y_2531_ = v_a_2507_;
v___y_2532_ = v_a_2508_;
v___y_2533_ = v_a_2509_;
v___y_2534_ = v_a_2510_;
v___y_2535_ = v_a_2511_;
v___y_2536_ = v_a_2512_;
v___y_2537_ = v_a_2513_;
v___y_2538_ = v_a_2514_;
v___y_2539_ = v_a_2515_;
v___y_2540_ = v_a_2516_;
goto v___jp_2529_;
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec_ref(v_appArgs_2528_);
lean_dec_ref(v_body_2523_);
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2721_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2721_);
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
}
}
v___jp_2529_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = lean_unsigned_to_nat(1u);
v___x_2542_ = lean_mk_empty_array_with_capacity(v___x_2541_);
v___x_2543_ = lean_array_push(v___x_2542_, v_value_2522_);
v___x_2544_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_2523_, v___x_2543_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v___x_2546_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref_known(v___x_2544_, 1);
v___x_2546_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_a_2545_, v_appArgs_2528_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec_ref(v_appArgs_2528_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; 
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2504_, v_info_2505_, v_a_2547_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2557_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2557_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2553_, 0, v_a_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_a_2558_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2548_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2548_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v_a_2566_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2546_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2546_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec_ref(v_appArgs_2528_);
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v_a_2574_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2544_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2544_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
lean_dec_ref(v_body_2523_);
lean_dec_ref(v_value_2522_);
lean_dec_ref(v_type_2521_);
lean_dec(v_declName_2520_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v_a_2730_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2525_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2525_);
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
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_dec_ref(v___x_2519_);
lean_dec_ref(v___x_2518_);
lean_dec_ref(v_info_2505_);
lean_dec(v_goal_2504_);
v___x_2738_ = lean_box(0);
v___x_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object* v_goal_2740_, lean_object* v_info_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_2740_, v_info_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_);
lean_dec(v_a_2752_);
lean_dec_ref(v_a_2751_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_2755_, lean_object* v_start_2756_, lean_object* v_b_2757_, lean_object* v_i_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2755_, v_start_2756_, v_b_2757_, v_i_2758_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_2772_, lean_object* v_start_2773_, lean_object* v_b_2774_, lean_object* v_i_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_2772_, v_start_2773_, v_b_2774_, v_i_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v_start_2773_);
lean_dec_ref(v_revArgs_2772_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_2789_, lean_object* v_b_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
if (lean_obj_tag(v_as_x27_2789_) == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_b_2790_);
return v___x_2800_;
}
else
{
lean_object* v_head_2801_; lean_object* v_tail_2802_; lean_object* v___x_2803_; 
v_head_2801_ = lean_ctor_get(v_as_x27_2789_, 0);
v_tail_2802_ = lean_ctor_get(v_as_x27_2789_, 1);
lean_inc(v_head_2801_);
v___x_2803_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_head_2801_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
switch(lean_obj_tag(v_a_2804_))
{
case 0:
{
lean_object* v___x_2805_; 
lean_inc(v_head_2801_);
v___x_2805_ = lean_array_push(v_b_2790_, v_head_2801_);
v_as_x27_2789_ = v_tail_2802_;
v_b_2790_ = v___x_2805_;
goto _start;
}
case 1:
{
v_as_x27_2789_ = v_tail_2802_;
goto _start;
}
default: 
{
lean_object* v_mvarId_2808_; lean_object* v___x_2809_; 
v_mvarId_2808_ = lean_ctor_get(v_a_2804_, 0);
lean_inc(v_mvarId_2808_);
lean_dec_ref_known(v_a_2804_, 1);
v___x_2809_ = lean_array_push(v_b_2790_, v_mvarId_2808_);
v_as_x27_2789_ = v_tail_2802_;
v_b_2790_ = v___x_2809_;
goto _start;
}
}
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec_ref(v_b_2790_);
v_a_2811_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___x_2803_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___x_2803_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_2819_, lean_object* v_b_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_2819_, v_b_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v___y_2822_);
lean_dec_ref(v___y_2821_);
lean_dec(v_as_x27_2819_);
return v_res_2830_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2));
v___x_2836_ = l_Lean_stringToMessageData(v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object* v_goal_2837_, lean_object* v_info_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_2838_);
lean_inc_ref(v___x_2851_);
v___x_2852_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_2851_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2995_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2855_ = v___x_2852_;
v_isShared_2856_ = v_isSharedCheck_2995_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_a_2853_);
lean_dec(v___x_2852_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2995_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
if (lean_obj_tag(v_a_2853_) == 1)
{
lean_object* v_val_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2990_; 
lean_del_object(v___x_2855_);
v_val_2857_ = lean_ctor_get(v_a_2853_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_a_2853_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2859_ = v_a_2853_;
v_isShared_2860_ = v_isSharedCheck_2990_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_val_2857_);
lean_dec(v_a_2853_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2990_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; 
if (lean_obj_tag(v_val_2857_) == 2)
{
lean_object* v_keyedConfig_2929_; uint8_t v_trackZetaDelta_2930_; lean_object* v_zetaDeltaSet_2931_; lean_object* v_lctx_2932_; lean_object* v_localInstances_2933_; lean_object* v_defEqCtx_x3f_2934_; lean_object* v_synthPendingDepth_2935_; lean_object* v_customCanUnfoldPredicate_x3f_2936_; uint8_t v_univApprox_2937_; uint8_t v_inTypeClassResolution_2938_; uint8_t v_cacheInferType_2939_; uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_keyedConfig_2929_ = lean_ctor_get(v_a_2846_, 0);
v_trackZetaDelta_2930_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7);
v_zetaDeltaSet_2931_ = lean_ctor_get(v_a_2846_, 1);
v_lctx_2932_ = lean_ctor_get(v_a_2846_, 2);
v_localInstances_2933_ = lean_ctor_get(v_a_2846_, 3);
v_defEqCtx_x3f_2934_ = lean_ctor_get(v_a_2846_, 4);
v_synthPendingDepth_2935_ = lean_ctor_get(v_a_2846_, 5);
v_customCanUnfoldPredicate_x3f_2936_ = lean_ctor_get(v_a_2846_, 6);
v_univApprox_2937_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2938_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7 + 2);
v_cacheInferType_2939_ = lean_ctor_get_uint8(v_a_2846_, sizeof(void*)*7 + 3);
v___x_2940_ = 2;
lean_inc_ref(v_keyedConfig_2929_);
v___x_2941_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2940_, v_keyedConfig_2929_);
lean_inc(v_customCanUnfoldPredicate_x3f_2936_);
lean_inc(v_synthPendingDepth_2935_);
lean_inc(v_defEqCtx_x3f_2934_);
lean_inc_ref(v_localInstances_2933_);
lean_inc_ref(v_lctx_2932_);
lean_inc(v_zetaDeltaSet_2931_);
v___x_2942_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v_zetaDeltaSet_2931_);
lean_ctor_set(v___x_2942_, 2, v_lctx_2932_);
lean_ctor_set(v___x_2942_, 3, v_localInstances_2933_);
lean_ctor_set(v___x_2942_, 4, v_defEqCtx_x3f_2934_);
lean_ctor_set(v___x_2942_, 5, v_synthPendingDepth_2935_);
lean_ctor_set(v___x_2942_, 6, v_customCanUnfoldPredicate_x3f_2936_);
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*7, v_trackZetaDelta_2930_);
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*7 + 1, v_univApprox_2937_);
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2938_);
lean_ctor_set_uint8(v___x_2942_, sizeof(void*)*7 + 3, v_cacheInferType_2939_);
v___x_2943_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_2851_, v___x_2942_, v_a_2847_, v_a_2848_, v_a_2849_);
lean_dec_ref_known(v___x_2942_, 7);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
if (lean_obj_tag(v_a_2944_) == 1)
{
lean_object* v_val_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2981_; 
lean_dec_ref_known(v_val_2857_, 1);
lean_del_object(v___x_2859_);
lean_dec_ref(v___x_2851_);
v_val_2945_ = lean_ctor_get(v_a_2944_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v_a_2944_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2947_ = v_a_2944_;
v_isShared_2948_ = v_isSharedCheck_2981_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_val_2945_);
lean_dec(v_a_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2981_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2945_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___x_2951_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2951_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2837_, v_info_2838_, v_a_2950_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2964_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2964_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2964_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2957_, 0, v_a_2952_);
lean_ctor_set(v___x_2957_, 1, v___x_2956_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 0, v___x_2957_);
v___x_2959_ = v___x_2947_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2957_);
v___x_2959_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2961_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v___x_2959_);
v___x_2961_ = v___x_2954_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
return v___x_2961_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_del_object(v___x_2947_);
v_a_2965_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2951_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2951_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2970_; 
if (v_isShared_2968_ == 0)
{
v___x_2970_ = v___x_2967_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v_a_2965_);
v___x_2970_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
return v___x_2970_;
}
}
}
}
else
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_2980_; 
lean_del_object(v___x_2947_);
lean_dec_ref(v_info_2838_);
lean_dec(v_goal_2837_);
v_a_2973_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2975_ = v___x_2949_;
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2949_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_2980_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v___x_2978_; 
if (v_isShared_2976_ == 0)
{
v___x_2978_ = v___x_2975_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v_a_2973_);
v___x_2978_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
return v___x_2978_;
}
}
}
}
}
else
{
lean_dec(v_a_2944_);
v___y_2862_ = v_a_2839_;
v___y_2863_ = v_a_2840_;
v___y_2864_ = v_a_2841_;
v___y_2865_ = v_a_2842_;
v___y_2866_ = v_a_2843_;
v___y_2867_ = v_a_2844_;
v___y_2868_ = v_a_2845_;
v___y_2869_ = v_a_2846_;
v___y_2870_ = v_a_2847_;
v___y_2871_ = v_a_2848_;
v___y_2872_ = v_a_2849_;
goto v___jp_2861_;
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_dec_ref_known(v_val_2857_, 1);
lean_del_object(v___x_2859_);
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_info_2838_);
lean_dec(v_goal_2837_);
v_a_2982_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2943_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2943_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
else
{
v___y_2862_ = v_a_2839_;
v___y_2863_ = v_a_2840_;
v___y_2864_ = v_a_2841_;
v___y_2865_ = v_a_2842_;
v___y_2866_ = v_a_2843_;
v___y_2867_ = v_a_2844_;
v___y_2868_ = v_a_2845_;
v___y_2869_ = v_a_2846_;
v___y_2870_ = v_a_2847_;
v___y_2871_ = v_a_2848_;
v___y_2872_ = v_a_2849_;
goto v___jp_2861_;
}
v___jp_2861_:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_2857_, v_info_2838_, v___y_2863_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1);
v___x_2876_ = l_Lean_indentExpr(v___x_2851_);
lean_inc_ref(v___x_2876_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2877_);
v___x_2879_ = v___x_2859_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2874_, v_goal_2837_, v___x_2879_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
if (lean_obj_tag(v_a_2881_) == 1)
{
lean_object* v_mvarIds_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___x_2876_);
v_mvarIds_2882_ = lean_ctor_get(v_a_2881_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_a_2881_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2884_ = v_a_2881_;
v_isShared_2885_ = v_isSharedCheck_2908_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_mvarIds_2882_);
lean_dec(v_a_2881_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2908_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2887_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_2882_, v___x_2886_, v___y_2862_, v___y_2863_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v_mvarIds_2882_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2899_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2899_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2899_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2892_; lean_object* v___x_2894_; 
v___x_2892_ = lean_array_to_list(v_a_2888_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2892_);
v___x_2894_ = v___x_2884_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2892_);
v___x_2894_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
lean_object* v___x_2896_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set(v___x_2890_, 0, v___x_2894_);
v___x_2896_ = v___x_2890_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2894_);
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
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_del_object(v___x_2884_);
v_a_2900_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2887_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2887_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
lean_dec(v_a_2881_);
v___x_2909_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
lean_ctor_set(v___x_2910_, 1, v___x_2876_);
v___x_2911_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2910_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
return v___x_2911_;
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___x_2876_);
v_a_2912_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2880_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2880_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_del_object(v___x_2859_);
lean_dec_ref(v___x_2851_);
lean_dec(v_goal_2837_);
v_a_2921_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2873_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2873_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
}
else
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_dec(v_a_2853_);
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_info_2838_);
lean_dec(v_goal_2837_);
v___x_2991_ = lean_box(0);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2991_);
v___x_2993_ = v___x_2855_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v___x_2851_);
lean_dec_ref(v_info_2838_);
lean_dec(v_goal_2837_);
v_a_2996_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2852_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2852_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3004_, lean_object* v_info_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_, lean_object* v_a_3008_, lean_object* v_a_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_3004_, v_info_3005_, v_a_3006_, v_a_3007_, v_a_3008_, v_a_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_a_3009_);
lean_dec(v_a_3008_);
lean_dec(v_a_3007_);
lean_dec_ref(v_a_3006_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3019_, lean_object* v_as_x27_3020_, lean_object* v_b_3021_, lean_object* v_a_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3020_, v_b_3021_, v___y_3023_, v___y_3024_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3036_, lean_object* v_as_x27_3037_, lean_object* v_b_3038_, lean_object* v_a_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(v_as_3036_, v_as_x27_3037_, v_b_3038_, v_a_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v_as_x27_3037_);
lean_dec(v_as_3036_);
return v_res_3052_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3055_ = l_Lean_stringToMessageData(v___x_3054_);
return v___x_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3056_, lean_object* v_info_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_){
_start:
{
lean_object* v___x_3070_; lean_object* v_f_3071_; lean_object* v___x_3072_; 
v___x_3070_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3057_);
v_f_3071_ = l_Lean_Expr_getAppFn(v___x_3070_);
v___x_3072_ = l_Lean_Expr_fvarId_x3f(v_f_3071_);
lean_dec_ref(v_f_3071_);
if (lean_obj_tag(v___x_3072_) == 1)
{
lean_object* v_val_3073_; uint8_t v___x_3074_; lean_object* v___x_3075_; 
v_val_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc_n(v_val_3073_, 2);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3074_ = 0;
v___x_3075_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3073_, v___x_3074_, v_a_3065_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3163_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3078_ = v___x_3075_;
v_isShared_3079_ = v_isSharedCheck_3163_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3163_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
if (lean_obj_tag(v_a_3076_) == 1)
{
lean_object* v_val_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3158_; 
lean_del_object(v___x_3078_);
v_val_3080_ = lean_ctor_get(v_a_3076_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v_a_3076_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3082_ = v_a_3076_;
v_isShared_3083_ = v_isSharedCheck_3158_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_val_3080_);
lean_dec(v_a_3076_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3158_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v_options_3130_; uint8_t v_hasTrace_3131_; 
v_options_3130_ = lean_ctor_get(v_a_3067_, 2);
v_hasTrace_3131_ = lean_ctor_get_uint8(v_options_3130_, sizeof(void*)*1);
if (v_hasTrace_3131_ == 0)
{
lean_dec(v_val_3073_);
v___y_3085_ = v_a_3058_;
v___y_3086_ = v_a_3059_;
v___y_3087_ = v_a_3060_;
v___y_3088_ = v_a_3061_;
v___y_3089_ = v_a_3062_;
v___y_3090_ = v_a_3063_;
v___y_3091_ = v_a_3064_;
v___y_3092_ = v_a_3065_;
v___y_3093_ = v_a_3066_;
v___y_3094_ = v_a_3067_;
v___y_3095_ = v_a_3068_;
goto v___jp_3084_;
}
else
{
lean_object* v_inheritedTraceOptions_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; uint8_t v___x_3135_; 
v_inheritedTraceOptions_3132_ = lean_ctor_get(v_a_3067_, 13);
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3134_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3135_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3132_, v_options_3130_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec(v_val_3073_);
v___y_3085_ = v_a_3058_;
v___y_3086_ = v_a_3059_;
v___y_3087_ = v_a_3060_;
v___y_3088_ = v_a_3061_;
v___y_3089_ = v_a_3062_;
v___y_3090_ = v_a_3063_;
v___y_3091_ = v_a_3064_;
v___y_3092_ = v_a_3065_;
v___y_3093_ = v_a_3066_;
v___y_3094_ = v_a_3067_;
v___y_3095_ = v_a_3068_;
goto v___jp_3084_;
}
else
{
lean_object* v___x_3136_; 
v___x_3136_ = l_Lean_FVarId_getUserName___redArg(v_val_3073_, v_a_3065_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3136_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___x_3136_, 1);
v___x_3138_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3139_ = l_Lean_MessageData_ofName(v_a_3137_);
v___x_3140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3138_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3133_, v___x_3140_, v_a_3065_, v_a_3066_, v_a_3067_, v_a_3068_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_dec_ref_known(v___x_3141_, 1);
v___y_3085_ = v_a_3058_;
v___y_3086_ = v_a_3059_;
v___y_3087_ = v_a_3060_;
v___y_3088_ = v_a_3061_;
v___y_3089_ = v_a_3062_;
v___y_3090_ = v_a_3063_;
v___y_3091_ = v_a_3064_;
v___y_3092_ = v_a_3065_;
v___y_3093_ = v_a_3066_;
v___y_3094_ = v_a_3067_;
v___y_3095_ = v_a_3068_;
goto v___jp_3084_;
}
else
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
lean_del_object(v___x_3082_);
lean_dec(v_val_3080_);
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_info_3057_);
lean_dec(v_goal_3056_);
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
lean_del_object(v___x_3082_);
lean_dec(v_val_3080_);
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_info_3057_);
lean_dec(v_goal_3056_);
v_a_3150_ = lean_ctor_get(v___x_3136_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3136_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3136_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3136_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
v___jp_3084_:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3096_ = l_Lean_Expr_getAppNumArgs(v___x_3070_);
v___x_3097_ = lean_mk_empty_array_with_capacity(v___x_3096_);
lean_dec(v___x_3096_);
v___x_3098_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3070_, v___x_3097_);
v___x_3099_ = l_Lean_Expr_betaRev(v_val_3080_, v___x_3098_, v___x_3074_, v___x_3074_);
lean_dec_ref(v___x_3098_);
v___x_3100_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3099_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3102_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
v___x_3102_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3056_, v_info_3057_, v_a_3101_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_, v___y_3095_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3113_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3105_ = v___x_3102_;
v_isShared_3106_ = v_isSharedCheck_3113_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3102_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3113_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3083_ == 0)
{
lean_ctor_set(v___x_3082_, 0, v_a_3103_);
v___x_3108_ = v___x_3082_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3110_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v___x_3108_);
v___x_3110_ = v___x_3105_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3108_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_del_object(v___x_3082_);
v_a_3114_ = lean_ctor_get(v___x_3102_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3102_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3102_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3102_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_del_object(v___x_3082_);
lean_dec_ref(v_info_3057_);
lean_dec(v_goal_3056_);
v_a_3122_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3100_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3100_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
lean_dec(v_a_3076_);
lean_dec(v_val_3073_);
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_info_3057_);
lean_dec(v_goal_3056_);
v___x_3159_ = lean_box(0);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3159_);
v___x_3161_ = v___x_3078_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec(v_val_3073_);
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_info_3057_);
lean_dec(v_goal_3056_);
v_a_3164_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3075_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3075_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
else
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec(v___x_3072_);
lean_dec_ref(v___x_3070_);
lean_dec_ref(v_info_3057_);
lean_dec(v_goal_3056_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3174_, lean_object* v_info_3175_, lean_object* v_a_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v_res_3188_; 
v_res_3188_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_3174_, v_info_3175_, v_a_3176_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_);
lean_dec(v_a_3186_);
lean_dec_ref(v_a_3185_);
lean_dec(v_a_3184_);
lean_dec_ref(v_a_3183_);
lean_dec(v_a_3182_);
lean_dec_ref(v_a_3181_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec(v_a_3177_);
lean_dec_ref(v_a_3176_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3189_, lean_object* v_info_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v___x_3203_; lean_object* v_a_3205_; lean_object* v_f_3266_; 
v___x_3203_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3190_);
v_f_3266_ = l_Lean_Expr_getAppFn(v___x_3203_);
if (lean_obj_tag(v_f_3266_) == 11)
{
lean_object* v_keyedConfig_3267_; uint8_t v_trackZetaDelta_3268_; lean_object* v_zetaDeltaSet_3269_; lean_object* v_lctx_3270_; lean_object* v_localInstances_3271_; lean_object* v_defEqCtx_x3f_3272_; lean_object* v_synthPendingDepth_3273_; lean_object* v_customCanUnfoldPredicate_x3f_3274_; uint8_t v_univApprox_3275_; uint8_t v_inTypeClassResolution_3276_; uint8_t v_cacheInferType_3277_; uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_keyedConfig_3267_ = lean_ctor_get(v_a_3198_, 0);
v_trackZetaDelta_3268_ = lean_ctor_get_uint8(v_a_3198_, sizeof(void*)*7);
v_zetaDeltaSet_3269_ = lean_ctor_get(v_a_3198_, 1);
v_lctx_3270_ = lean_ctor_get(v_a_3198_, 2);
v_localInstances_3271_ = lean_ctor_get(v_a_3198_, 3);
v_defEqCtx_x3f_3272_ = lean_ctor_get(v_a_3198_, 4);
v_synthPendingDepth_3273_ = lean_ctor_get(v_a_3198_, 5);
v_customCanUnfoldPredicate_x3f_3274_ = lean_ctor_get(v_a_3198_, 6);
v_univApprox_3275_ = lean_ctor_get_uint8(v_a_3198_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3276_ = lean_ctor_get_uint8(v_a_3198_, sizeof(void*)*7 + 2);
v_cacheInferType_3277_ = lean_ctor_get_uint8(v_a_3198_, sizeof(void*)*7 + 3);
v___x_3278_ = 3;
lean_inc_ref(v_keyedConfig_3267_);
v___x_3279_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3278_, v_keyedConfig_3267_);
lean_inc(v_customCanUnfoldPredicate_x3f_3274_);
lean_inc(v_synthPendingDepth_3273_);
lean_inc(v_defEqCtx_x3f_3272_);
lean_inc_ref(v_localInstances_3271_);
lean_inc_ref(v_lctx_3270_);
lean_inc(v_zetaDeltaSet_3269_);
v___x_3280_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v_zetaDeltaSet_3269_);
lean_ctor_set(v___x_3280_, 2, v_lctx_3270_);
lean_ctor_set(v___x_3280_, 3, v_localInstances_3271_);
lean_ctor_set(v___x_3280_, 4, v_defEqCtx_x3f_3272_);
lean_ctor_set(v___x_3280_, 5, v_synthPendingDepth_3273_);
lean_ctor_set(v___x_3280_, 6, v_customCanUnfoldPredicate_x3f_3274_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*7, v_trackZetaDelta_3268_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*7 + 1, v_univApprox_3275_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3276_);
lean_ctor_set_uint8(v___x_3280_, sizeof(void*)*7 + 3, v_cacheInferType_3277_);
v___x_3281_ = l_Lean_Meta_reduceProj_x3f(v_f_3266_, v___x_3280_, v_a_3199_, v_a_3200_, v_a_3201_);
lean_dec_ref_known(v___x_3280_, 7);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v_a_3205_ = v_a_3282_;
goto v___jp_3204_;
}
else
{
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3283_; 
v_a_3283_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3283_);
lean_dec_ref_known(v___x_3281_, 1);
v_a_3205_ = v_a_3283_;
goto v___jp_3204_;
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec_ref(v___x_3203_);
lean_dec_ref(v_info_3190_);
lean_dec(v_goal_3189_);
v_a_3284_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3281_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3281_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
lean_dec_ref(v_f_3266_);
lean_dec_ref(v___x_3203_);
lean_dec_ref(v_info_3190_);
lean_dec(v_goal_3189_);
v___x_3292_ = lean_box(0);
v___x_3293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
return v___x_3293_;
}
v___jp_3204_:
{
if (lean_obj_tag(v_a_3205_) == 1)
{
lean_object* v_val_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3263_; 
v_val_3206_ = lean_ctor_get(v_a_3205_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_a_3205_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3208_ = v_a_3205_;
v_isShared_3209_ = v_isSharedCheck_3263_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_val_3206_);
lean_dec(v_a_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3263_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3206_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_Meta_Sym_shareCommon(v_a_3211_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v___x_3214_ = l_Lean_Expr_getAppNumArgs(v___x_3203_);
v___x_3215_ = lean_mk_empty_array_with_capacity(v___x_3214_);
lean_dec(v___x_3214_);
v___x_3216_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3203_, v___x_3215_);
v___x_3217_ = l_Lean_Meta_Sym_betaRevS(v_a_3213_, v___x_3216_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3189_, v_info_3190_, v_a_3218_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3230_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3230_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3230_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3230_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3209_ == 0)
{
lean_ctor_set(v___x_3208_, 0, v_a_3220_);
v___x_3225_ = v___x_3208_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3227_; 
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3225_);
v___x_3227_ = v___x_3222_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
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
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_del_object(v___x_3208_);
v_a_3231_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3219_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3219_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
else
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_del_object(v___x_3208_);
lean_dec_ref(v_info_3190_);
lean_dec(v_goal_3189_);
v_a_3239_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3217_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3217_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_del_object(v___x_3208_);
lean_dec_ref(v___x_3203_);
lean_dec_ref(v_info_3190_);
lean_dec(v_goal_3189_);
v_a_3247_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3212_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3212_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_del_object(v___x_3208_);
lean_dec_ref(v___x_3203_);
lean_dec_ref(v_info_3190_);
lean_dec(v_goal_3189_);
v_a_3255_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3210_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3210_);
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
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_a_3205_);
lean_dec_ref(v___x_3203_);
lean_dec_ref(v_info_3190_);
lean_dec(v_goal_3189_);
v___x_3264_ = lean_box(0);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
return v___x_3265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_3294_, lean_object* v_info_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_3294_, v_info_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec_ref(v_a_3305_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
lean_dec(v_a_3298_);
lean_dec(v_a_3297_);
lean_dec_ref(v_a_3296_);
return v_res_3308_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_3317_ = l_Lean_stringToMessageData(v___x_3316_);
return v___x_3317_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_3320_ = l_Lean_stringToMessageData(v___x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_3321_, lean_object* v_a_3322_){
_start:
{
if (lean_obj_tag(v_a_3321_) == 0)
{
lean_object* v___x_3323_; 
v___x_3323_ = l_List_reverse___redArg(v_a_3322_);
return v___x_3323_;
}
else
{
lean_object* v_head_3324_; lean_object* v_tail_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3353_; 
v_head_3324_ = lean_ctor_get(v_a_3321_, 0);
v_tail_3325_ = lean_ctor_get(v_a_3321_, 1);
v_isSharedCheck_3353_ = !lean_is_exclusive(v_a_3321_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3327_ = v_a_3321_;
v_isShared_3328_ = v_isSharedCheck_3353_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_tail_3325_);
lean_inc(v_head_3324_);
lean_dec(v_a_3321_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3353_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___y_3330_; 
switch(lean_obj_tag(v_head_3324_))
{
case 0:
{
lean_object* v_declName_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_declName_3335_ = lean_ctor_get(v_head_3324_, 0);
lean_inc(v_declName_3335_);
lean_dec_ref_known(v_head_3324_, 1);
v___x_3336_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3337_ = l_Lean_MessageData_ofName(v_declName_3335_);
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3336_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___y_3330_ = v___x_3338_;
goto v___jp_3329_;
}
case 1:
{
lean_object* v_fvarId_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_fvarId_3339_ = lean_ctor_get(v_head_3324_, 0);
lean_inc(v_fvarId_3339_);
lean_dec_ref_known(v_head_3324_, 1);
v___x_3340_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3341_ = l_Lean_mkFVar(v_fvarId_3339_);
v___x_3342_ = l_Lean_MessageData_ofExpr(v___x_3341_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3340_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___y_3330_ = v___x_3343_;
goto v___jp_3329_;
}
default: 
{
lean_object* v_ref_3344_; lean_object* v_proof_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_ref_3344_ = lean_ctor_get(v_head_3324_, 1);
lean_inc(v_ref_3344_);
v_proof_3345_ = lean_ctor_get(v_head_3324_, 2);
lean_inc_ref(v_proof_3345_);
lean_dec_ref_known(v_head_3324_, 3);
v___x_3346_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3347_ = l_Lean_MessageData_ofSyntax(v_ref_3344_);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = l_Lean_MessageData_ofExpr(v_proof_3345_);
v___x_3352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___y_3330_ = v___x_3352_;
goto v___jp_3329_;
}
}
v___jp_3329_:
{
lean_object* v___x_3332_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set(v___x_3327_, 1, v_a_3322_);
lean_ctor_set(v___x_3327_, 0, v___y_3330_);
v___x_3332_ = v___x_3327_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___y_3330_);
lean_ctor_set(v_reuseFailAlloc_3334_, 1, v_a_3322_);
v___x_3332_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
v_a_3321_ = v_tail_3325_;
v_a_3322_ = v___x_3332_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_3354_, size_t v_i_3355_, lean_object* v_bs_3356_){
_start:
{
uint8_t v___x_3357_; 
v___x_3357_ = lean_usize_dec_lt(v_i_3355_, v_sz_3354_);
if (v___x_3357_ == 0)
{
return v_bs_3356_;
}
else
{
lean_object* v_v_3358_; lean_object* v_proof_3359_; lean_object* v___x_3360_; lean_object* v_bs_x27_3361_; size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; 
v_v_3358_ = lean_array_uget_borrowed(v_bs_3356_, v_i_3355_);
v_proof_3359_ = lean_ctor_get(v_v_3358_, 1);
lean_inc_ref(v_proof_3359_);
v___x_3360_ = lean_unsigned_to_nat(0u);
v_bs_x27_3361_ = lean_array_uset(v_bs_3356_, v_i_3355_, v___x_3360_);
v___x_3362_ = ((size_t)1ULL);
v___x_3363_ = lean_usize_add(v_i_3355_, v___x_3362_);
v___x_3364_ = lean_array_uset(v_bs_x27_3361_, v_i_3355_, v_proof_3359_);
v_i_3355_ = v___x_3363_;
v_bs_3356_ = v___x_3364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_3366_, lean_object* v_i_3367_, lean_object* v_bs_3368_){
_start:
{
size_t v_sz_boxed_3369_; size_t v_i_boxed_3370_; lean_object* v_res_3371_; 
v_sz_boxed_3369_ = lean_unbox_usize(v_sz_3366_);
lean_dec(v_sz_3366_);
v_i_boxed_3370_ = lean_unbox_usize(v_i_3367_);
lean_dec(v_i_3367_);
v_res_3371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_3369_, v_i_boxed_3370_, v_bs_3368_);
return v_res_3371_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_3374_ = l_Lean_stringToMessageData(v___x_3373_);
return v___x_3374_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_3377_ = l_Lean_stringToMessageData(v___x_3376_);
return v___x_3377_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_3380_ = l_Lean_stringToMessageData(v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_3383_ = l_Lean_stringToMessageData(v___x_3382_);
return v___x_3383_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_3386_ = l_Lean_stringToMessageData(v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_3387_, lean_object* v_monad_3388_, lean_object* v_thms_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_){
_start:
{
uint8_t v_errorOnMissingSpec_3396_; 
v_errorOnMissingSpec_3396_ = lean_ctor_get_uint8(v_a_3390_, sizeof(void*)*6 + 2);
if (v_errorOnMissingSpec_3396_ == 0)
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_3397_, 0, v_prog_3387_);
lean_ctor_set(v___x_3397_, 1, v_monad_3388_);
lean_ctor_set(v___x_3397_, 2, v_thms_3389_);
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
v___x_3399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3398_);
return v___x_3399_;
}
else
{
lean_object* v___x_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3400_ = lean_array_get_size(v_thms_3389_);
v___x_3401_ = lean_unsigned_to_nat(0u);
v___x_3402_ = lean_nat_dec_eq(v___x_3400_, v___x_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; size_t v_sz_3412_; size_t v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
v___x_3403_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_3404_ = l_Lean_MessageData_ofExpr(v_monad_3388_);
v___x_3405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_3407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = l_Lean_MessageData_ofExpr(v_prog_3387_);
v___x_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3407_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3409_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v_sz_3412_ = lean_array_size(v_thms_3389_);
v___x_3413_ = ((size_t)0ULL);
v___x_3414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_3412_, v___x_3413_, v_thms_3389_);
v___x_3415_ = lean_array_to_list(v___x_3414_);
v___x_3416_ = lean_box(0);
v___x_3417_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_3415_, v___x_3416_);
v___x_3418_ = l_Lean_MessageData_ofList(v___x_3417_);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3411_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3421_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
return v___x_3422_;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_dec_ref(v_thms_3389_);
lean_dec_ref(v_monad_3388_);
v___x_3423_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_3424_ = l_Lean_MessageData_ofExpr(v_prog_3387_);
v___x_3425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3427_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_);
return v___x_3428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_3429_, lean_object* v_monad_3430_, lean_object* v_thms_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3429_, v_monad_3430_, v_thms_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec_ref(v_a_3432_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_3439_, lean_object* v_monad_3440_, lean_object* v_thms_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3439_, v_monad_3440_, v_thms_3441_, v_a_3442_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_3455_, lean_object* v_monad_3456_, lean_object* v_thms_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(v_prog_3455_, v_monad_3456_, v_thms_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec(v_a_3459_);
lean_dec_ref(v_a_3458_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(lean_object* v_scope_3471_, lean_object* v_prog_3472_, lean_object* v_monad_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
lean_object* v_specs_3482_; lean_object* v_jps_3483_; lean_object* v_lastLiftedPre_x3f_3484_; lean_object* v_nextDeclIdx_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3554_; 
v_specs_3482_ = lean_ctor_get(v_scope_3471_, 0);
v_jps_3483_ = lean_ctor_get(v_scope_3471_, 1);
v_lastLiftedPre_x3f_3484_ = lean_ctor_get(v_scope_3471_, 2);
v_nextDeclIdx_3485_ = lean_ctor_get(v_scope_3471_, 3);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_scope_3471_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3487_ = v_scope_3471_;
v_isShared_3488_ = v_isSharedCheck_3554_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_nextDeclIdx_3485_);
lean_inc(v_lastLiftedPre_x3f_3484_);
lean_inc(v_jps_3483_);
lean_inc(v_specs_3482_);
lean_dec(v_scope_3471_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3554_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3489_; 
lean_inc_ref(v_prog_3472_);
v___x_3489_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(v_specs_3482_, v_prog_3472_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3545_; 
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3492_ = v___x_3489_;
v_isShared_3493_ = v_isSharedCheck_3545_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3489_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3545_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_fst_3494_; lean_object* v_snd_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3544_; 
v_fst_3494_ = lean_ctor_get(v_a_3490_, 0);
v_snd_3495_ = lean_ctor_get(v_a_3490_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3497_ = v_a_3490_;
v_isShared_3498_ = v_isSharedCheck_3544_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_snd_3495_);
lean_inc(v_fst_3494_);
lean_dec(v_a_3490_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3544_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3488_ == 0)
{
lean_ctor_set(v___x_3487_, 0, v_snd_3495_);
v___x_3500_ = v___x_3487_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_snd_3495_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v_jps_3483_);
lean_ctor_set(v_reuseFailAlloc_3543_, 2, v_lastLiftedPre_x3f_3484_);
lean_ctor_set(v_reuseFailAlloc_3543_, 3, v_nextDeclIdx_3485_);
v___x_3500_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
if (lean_obj_tag(v_fst_3494_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3528_; 
lean_del_object(v___x_3492_);
v_a_3501_ = lean_ctor_get(v_fst_3494_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_fst_3494_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3503_ = v_fst_3494_;
v_isShared_3504_ = v_isSharedCheck_3528_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v_fst_3494_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3528_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3472_, v_monad_3473_, v_a_3501_, v_a_3474_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3519_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3508_ = v___x_3505_;
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3505_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3519_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 0, v_a_3506_);
v___x_3511_ = v___x_3503_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 1, v___x_3511_);
lean_ctor_set(v___x_3497_, 0, v___x_3500_);
v___x_3513_ = v___x_3497_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3515_; 
if (v_isShared_3509_ == 0)
{
lean_ctor_set(v___x_3508_, 0, v___x_3513_);
v___x_3515_ = v___x_3508_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_del_object(v___x_3503_);
lean_dec_ref(v___x_3500_);
lean_del_object(v___x_3497_);
v_a_3520_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3505_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3505_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3542_; 
lean_dec_ref(v_monad_3473_);
lean_dec_ref(v_prog_3472_);
v_a_3529_ = lean_ctor_get(v_fst_3494_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v_fst_3494_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3531_ = v_fst_3494_;
v_isShared_3532_ = v_isSharedCheck_3542_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v_fst_3494_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3542_;
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
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
lean_object* v___x_3536_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 1, v___x_3534_);
lean_ctor_set(v___x_3497_, 0, v___x_3500_);
v___x_3536_ = v___x_3497_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v___x_3500_);
lean_ctor_set(v_reuseFailAlloc_3540_, 1, v___x_3534_);
v___x_3536_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3538_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 0, v___x_3536_);
v___x_3538_ = v___x_3492_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
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
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_del_object(v___x_3487_);
lean_dec(v_nextDeclIdx_3485_);
lean_dec(v_lastLiftedPre_x3f_3484_);
lean_dec(v_jps_3483_);
lean_dec_ref(v_monad_3473_);
lean_dec_ref(v_prog_3472_);
v_a_3546_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3489_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3489_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg___boxed(lean_object* v_scope_3555_, lean_object* v_prog_3556_, lean_object* v_monad_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(v_scope_3555_, v_prog_3556_, v_monad_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec_ref(v_a_3558_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec(lean_object* v_scope_3567_, lean_object* v_prog_3568_, lean_object* v_monad_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v___x_3582_; 
v___x_3582_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(v_scope_3567_, v_prog_3568_, v_monad_3569_, v_a_3570_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___boxed(lean_object* v_scope_3583_, lean_object* v_prog_3584_, lean_object* v_monad_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec(v_scope_3583_, v_prog_3584_, v_monad_3585_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_);
lean_dec(v_a_3596_);
lean_dec_ref(v_a_3595_);
lean_dec(v_a_3594_);
lean_dec_ref(v_a_3593_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec(v_a_3587_);
lean_dec_ref(v_a_3586_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
if (lean_obj_tag(v_a_3599_) == 0)
{
lean_object* v___x_3601_; 
v___x_3601_ = l_List_reverse___redArg(v_a_3600_);
return v___x_3601_;
}
else
{
lean_object* v_head_3602_; lean_object* v_tail_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
v_head_3602_ = lean_ctor_get(v_a_3599_, 0);
v_tail_3603_ = lean_ctor_get(v_a_3599_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_a_3599_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3605_ = v_a_3599_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_tail_3603_);
lean_inc(v_head_3602_);
lean_dec(v_a_3599_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = l_Lean_MessageData_ofExpr(v_head_3602_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set(v___x_3605_, 1, v_a_3600_);
lean_ctor_set(v___x_3605_, 0, v___x_3607_);
v___x_3609_ = v___x_3605_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_a_3600_);
v___x_3609_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
v_a_3599_ = v_tail_3603_;
v_a_3600_ = v___x_3609_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_3615_ = l_Lean_stringToMessageData(v___x_3614_);
return v___x_3615_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_3618_ = l_Lean_stringToMessageData(v___x_3617_);
return v___x_3618_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_3621_ = l_Lean_stringToMessageData(v___x_3620_);
return v___x_3621_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_3624_ = l_Lean_stringToMessageData(v___x_3623_);
return v___x_3624_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_3627_ = l_Lean_stringToMessageData(v___x_3626_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_3630_ = l_Lean_stringToMessageData(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_3633_ = l_Lean_stringToMessageData(v___x_3632_);
return v___x_3633_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_3639_ = l_Lean_stringToMessageData(v___x_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_3642_ = l_Lean_stringToMessageData(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_3644_; lean_object* v___x_3645_; 
v___x_3644_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_3645_ = l_Lean_stringToMessageData(v___x_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_scope_3646_, lean_object* v_goal_3647_, lean_object* v_info_3648_, lean_object* v_thm_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3668_; lean_object* v___y_3669_; lean_object* v___y_3670_; lean_object* v___y_3671_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; uint8_t v___y_3856_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v_options_3903_; uint8_t v_hasTrace_3904_; 
v_options_3903_ = lean_ctor_get(v_a_3659_, 2);
v_hasTrace_3904_ = lean_ctor_get_uint8(v_options_3903_, sizeof(void*)*1);
if (v_hasTrace_3904_ == 0)
{
v___y_3888_ = v_a_3650_;
v___y_3889_ = v_a_3651_;
v___y_3890_ = v_a_3652_;
v___y_3891_ = v_a_3653_;
v___y_3892_ = v_a_3654_;
v___y_3893_ = v_a_3655_;
v___y_3894_ = v_a_3656_;
v___y_3895_ = v_a_3657_;
v___y_3896_ = v_a_3658_;
v___y_3897_ = v_a_3659_;
v___y_3898_ = v_a_3660_;
goto v___jp_3887_;
}
else
{
lean_object* v_inheritedTraceOptions_3905_; lean_object* v_cls_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v_inheritedTraceOptions_3905_ = lean_ctor_get(v_a_3659_, 13);
v_cls_3906_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3905_, v_options_3903_, v___x_3907_);
if (v___x_3908_ == 0)
{
v___y_3888_ = v_a_3650_;
v___y_3889_ = v_a_3651_;
v___y_3890_ = v_a_3652_;
v___y_3891_ = v_a_3653_;
v___y_3892_ = v_a_3654_;
v___y_3893_ = v_a_3655_;
v___y_3894_ = v_a_3656_;
v___y_3895_ = v_a_3657_;
v___y_3896_ = v_a_3658_;
v___y_3897_ = v_a_3659_;
v___y_3898_ = v_a_3660_;
goto v___jp_3887_;
}
else
{
lean_object* v_proof_3909_; lean_object* v___x_3910_; lean_object* v___y_3912_; 
v_proof_3909_ = lean_ctor_get(v_thm_3649_, 1);
v___x_3910_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
switch(lean_obj_tag(v_proof_3909_))
{
case 0:
{
lean_object* v_declName_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
v_declName_3936_ = lean_ctor_get(v_proof_3909_, 0);
v___x_3937_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3936_);
v___x_3938_ = l_Lean_MessageData_ofName(v_declName_3936_);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___y_3912_ = v___x_3939_;
goto v___jp_3911_;
}
case 1:
{
lean_object* v_fvarId_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_fvarId_3940_ = lean_ctor_get(v_proof_3909_, 0);
v___x_3941_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3940_);
v___x_3942_ = l_Lean_mkFVar(v_fvarId_3940_);
v___x_3943_ = l_Lean_MessageData_ofExpr(v___x_3942_);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3941_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___y_3912_ = v___x_3944_;
goto v___jp_3911_;
}
default: 
{
lean_object* v_ref_3945_; lean_object* v_proof_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v_ref_3945_ = lean_ctor_get(v_proof_3909_, 1);
v_proof_3946_ = lean_ctor_get(v_proof_3909_, 2);
v___x_3947_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3945_);
v___x_3948_ = l_Lean_MessageData_ofSyntax(v_ref_3945_);
v___x_3949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
lean_inc_ref(v_proof_3946_);
v___x_3952_ = l_Lean_MessageData_ofExpr(v_proof_3946_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3951_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___y_3912_ = v___x_3953_;
goto v___jp_3911_;
}
}
v___jp_3911_:
{
lean_object* v_excessArgs_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_excessArgs_3913_ = lean_ctor_get(v_info_3648_, 2);
v___x_3914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3910_);
lean_ctor_set(v___x_3914_, 1, v___y_3912_);
v___x_3915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3914_);
lean_ctor_set(v___x_3916_, 1, v___x_3915_);
v___x_3917_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3648_);
v___x_3918_ = l_Lean_MessageData_ofExpr(v___x_3917_);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3916_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___x_3920_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_3921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
lean_inc_ref(v_excessArgs_3913_);
v___x_3922_ = lean_array_to_list(v_excessArgs_3913_);
v___x_3923_ = lean_box(0);
v___x_3924_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3922_, v___x_3923_);
v___x_3925_ = l_Lean_MessageData_ofList(v___x_3924_);
v___x_3926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3921_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3906_, v___x_3926_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_dec_ref_known(v___x_3927_, 1);
v___y_3888_ = v_a_3650_;
v___y_3889_ = v_a_3651_;
v___y_3890_ = v_a_3652_;
v___y_3891_ = v_a_3653_;
v___y_3892_ = v_a_3654_;
v___y_3893_ = v_a_3655_;
v___y_3894_ = v_a_3656_;
v___y_3895_ = v_a_3657_;
v___y_3896_ = v_a_3658_;
v___y_3897_ = v_a_3659_;
v___y_3898_ = v_a_3660_;
goto v___jp_3887_;
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
lean_dec(v_goal_3647_);
lean_dec_ref(v_scope_3646_);
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3927_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3927_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
}
v___jp_3662_:
{
lean_object* v_excessArgs_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v_excessArgs_3672_ = lean_ctor_get(v_info_3648_, 2);
lean_inc_ref(v_excessArgs_3672_);
lean_inc_ref(v___y_3667_);
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___y_3667_);
lean_ctor_set(v___x_3673_, 1, v___y_3671_);
v___x_3674_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3673_);
lean_ctor_set(v___x_3675_, 1, v___x_3674_);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
lean_ctor_set(v___x_3676_, 1, v___y_3663_);
v___x_3677_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3676_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = l_Lean_indentExpr(v___y_3666_);
v___x_3680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3680_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_3648_);
lean_dec_ref(v_info_3648_);
v___x_3684_ = l_Lean_indentExpr(v___x_3683_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3682_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3685_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = lean_array_to_list(v_excessArgs_3672_);
v___x_3689_ = lean_box(0);
v___x_3690_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3688_, v___x_3689_);
v___x_3691_ = l_Lean_MessageData_ofList(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3687_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = l_Lean_indentExpr(v___y_3665_);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3696_, v___y_3668_, v___y_3664_, v___y_3669_, v___y_3670_);
return v___x_3697_;
}
v___jp_3698_:
{
if (lean_obj_tag(v___y_3710_) == 0)
{
lean_object* v_a_3711_; 
v_a_3711_ = lean_ctor_get(v___y_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___y_3710_, 1);
if (lean_obj_tag(v_a_3711_) == 1)
{
lean_object* v_val_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3783_; 
v_val_3712_ = lean_ctor_get(v_a_3711_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_a_3711_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3714_ = v_a_3711_;
v_isShared_3715_ = v_isSharedCheck_3783_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_val_3712_);
lean_dec(v_a_3711_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3783_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3721_; 
v___x_3716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
v___x_3717_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3648_);
v___x_3718_ = l_Lean_indentExpr(v___x_3717_);
lean_inc_ref(v___x_3718_);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3716_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3719_);
v___x_3721_ = v___x_3714_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
lean_inc(v_goal_3647_);
lean_inc(v_val_3712_);
v___x_3722_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_3712_, v_goal_3647_, v___x_3721_, v___y_3699_, v___y_3703_, v___y_3707_, v___y_3702_, v___y_3701_, v___y_3705_, v___y_3704_, v___y_3706_, v___y_3700_, v___y_3708_, v___y_3709_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3773_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3725_ = v___x_3722_;
v_isShared_3726_ = v_isSharedCheck_3773_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3773_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
if (lean_obj_tag(v_a_3723_) == 1)
{
lean_object* v_mvarIds_3727_; lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_dec_ref(v___x_3718_);
lean_dec(v_val_3712_);
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
lean_dec(v_goal_3647_);
v_mvarIds_3727_ = lean_ctor_get(v_a_3723_, 0);
lean_inc(v_mvarIds_3727_);
lean_dec_ref_known(v_a_3723_, 1);
v___x_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3728_, 0, v_scope_3646_);
lean_ctor_set(v___x_3728_, 1, v_mvarIds_3727_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v___x_3728_);
v___x_3730_ = v___x_3725_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
else
{
lean_object* v_expr_3732_; lean_object* v___x_3733_; 
lean_del_object(v___x_3725_);
lean_dec(v_a_3723_);
lean_dec_ref(v_scope_3646_);
v_expr_3732_ = lean_ctor_get(v_val_3712_, 0);
lean_inc_ref(v_expr_3732_);
lean_dec(v_val_3712_);
lean_inc(v___y_3709_);
lean_inc_ref(v___y_3708_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3706_);
v___x_3733_ = lean_infer_type(v_expr_3732_, v___y_3706_, v___y_3700_, v___y_3708_, v___y_3709_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3735_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
lean_inc(v_a_3734_);
lean_dec_ref_known(v___x_3733_, 1);
v___x_3735_ = l_Lean_MVarId_getType(v_goal_3647_, v___y_3706_, v___y_3700_, v___y_3708_, v___y_3709_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_object* v_a_3736_; lean_object* v_proof_3737_; lean_object* v___x_3738_; 
v_a_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_a_3736_);
lean_dec_ref_known(v___x_3735_, 1);
v_proof_3737_ = lean_ctor_get(v_thm_3649_, 1);
lean_inc_ref(v_proof_3737_);
lean_dec_ref(v_thm_3649_);
v___x_3738_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
switch(lean_obj_tag(v_proof_3737_))
{
case 0:
{
lean_object* v_declName_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_declName_3739_ = lean_ctor_get(v_proof_3737_, 0);
lean_inc(v_declName_3739_);
lean_dec_ref_known(v_proof_3737_, 1);
v___x_3740_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3741_ = l_Lean_MessageData_ofName(v_declName_3739_);
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3740_);
lean_ctor_set(v___x_3742_, 1, v___x_3741_);
v___y_3663_ = v___x_3718_;
v___y_3664_ = v___y_3700_;
v___y_3665_ = v_a_3734_;
v___y_3666_ = v_a_3736_;
v___y_3667_ = v___x_3738_;
v___y_3668_ = v___y_3706_;
v___y_3669_ = v___y_3708_;
v___y_3670_ = v___y_3709_;
v___y_3671_ = v___x_3742_;
goto v___jp_3662_;
}
case 1:
{
lean_object* v_fvarId_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v_fvarId_3743_ = lean_ctor_get(v_proof_3737_, 0);
lean_inc(v_fvarId_3743_);
lean_dec_ref_known(v_proof_3737_, 1);
v___x_3744_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3745_ = l_Lean_mkFVar(v_fvarId_3743_);
v___x_3746_ = l_Lean_MessageData_ofExpr(v___x_3745_);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3744_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___y_3663_ = v___x_3718_;
v___y_3664_ = v___y_3700_;
v___y_3665_ = v_a_3734_;
v___y_3666_ = v_a_3736_;
v___y_3667_ = v___x_3738_;
v___y_3668_ = v___y_3706_;
v___y_3669_ = v___y_3708_;
v___y_3670_ = v___y_3709_;
v___y_3671_ = v___x_3747_;
goto v___jp_3662_;
}
default: 
{
lean_object* v_ref_3748_; lean_object* v_proof_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v_ref_3748_ = lean_ctor_get(v_proof_3737_, 1);
lean_inc(v_ref_3748_);
v_proof_3749_ = lean_ctor_get(v_proof_3737_, 2);
lean_inc_ref(v_proof_3749_);
lean_dec_ref_known(v_proof_3737_, 3);
v___x_3750_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3751_ = l_Lean_MessageData_ofSyntax(v_ref_3748_);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
v___x_3755_ = l_Lean_MessageData_ofExpr(v_proof_3749_);
v___x_3756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___y_3663_ = v___x_3718_;
v___y_3664_ = v___y_3700_;
v___y_3665_ = v_a_3734_;
v___y_3666_ = v_a_3736_;
v___y_3667_ = v___x_3738_;
v___y_3668_ = v___y_3706_;
v___y_3669_ = v___y_3708_;
v___y_3670_ = v___y_3709_;
v___y_3671_ = v___x_3756_;
goto v___jp_3662_;
}
}
}
else
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3764_; 
lean_dec(v_a_3734_);
lean_dec_ref(v___x_3718_);
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
v_a_3757_ = lean_ctor_get(v___x_3735_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3759_ = v___x_3735_;
v_isShared_3760_ = v_isSharedCheck_3764_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3735_);
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
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v___x_3718_);
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
lean_dec(v_goal_3647_);
v_a_3765_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3733_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3733_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_dec_ref(v___x_3718_);
lean_dec(v_val_3712_);
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
lean_dec(v_goal_3647_);
lean_dec_ref(v_scope_3646_);
v_a_3774_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3722_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3722_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
lean_dec(v_a_3711_);
lean_dec(v_goal_3647_);
lean_dec_ref(v_scope_3646_);
v___x_3784_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3648_);
v___x_3785_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_3648_);
lean_dec_ref(v_info_3648_);
v___x_3786_ = lean_unsigned_to_nat(1u);
v___x_3787_ = lean_mk_empty_array_with_capacity(v___x_3786_);
v___x_3788_ = lean_array_push(v___x_3787_, v_thm_3649_);
v___x_3789_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3784_, v___x_3785_, v___x_3788_, v___y_3699_, v___y_3706_, v___y_3700_, v___y_3708_, v___y_3709_);
return v___x_3789_;
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
lean_dec(v_goal_3647_);
lean_dec_ref(v_scope_3646_);
v_a_3790_ = lean_ctor_get(v___y_3710_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___y_3710_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___y_3710_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___y_3710_);
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
v___jp_3798_:
{
lean_object* v_excessArgs_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_excessArgs_3814_ = lean_ctor_get(v_info_3648_, 2);
lean_inc_ref(v___y_3811_);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___y_3811_);
lean_ctor_set(v___x_3815_, 1, v___y_3813_);
v___x_3816_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3648_);
v___x_3819_ = l_Lean_indentExpr(v___x_3818_);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3817_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
v___x_3822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = l_Lean_Exception_toMessageData(v___y_3806_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = l_Lean_indentExpr(v___y_3807_);
v___x_3828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3827_);
v___x_3829_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3828_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_3648_);
v___x_3832_ = l_Lean_indentExpr(v___x_3831_);
v___x_3833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3830_);
lean_ctor_set(v___x_3833_, 1, v___x_3832_);
v___x_3834_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3835_, 0, v___x_3833_);
lean_ctor_set(v___x_3835_, 1, v___x_3834_);
lean_inc_ref(v_excessArgs_3814_);
v___x_3836_ = lean_array_to_list(v_excessArgs_3814_);
v___x_3837_ = lean_box(0);
v___x_3838_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3836_, v___x_3837_);
v___x_3839_ = l_Lean_MessageData_ofList(v___x_3838_);
v___x_3840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3835_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
v___x_3841_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3840_, v___y_3812_, v___y_3799_, v___y_3803_, v___y_3804_);
v___y_3699_ = v___y_3805_;
v___y_3700_ = v___y_3799_;
v___y_3701_ = v___y_3800_;
v___y_3702_ = v___y_3808_;
v___y_3703_ = v___y_3809_;
v___y_3704_ = v___y_3810_;
v___y_3705_ = v___y_3801_;
v___y_3706_ = v___y_3812_;
v___y_3707_ = v___y_3802_;
v___y_3708_ = v___y_3803_;
v___y_3709_ = v___y_3804_;
v___y_3710_ = v___x_3841_;
goto v___jp_3698_;
}
v___jp_3842_:
{
if (v___y_3856_ == 0)
{
lean_object* v___x_3857_; 
lean_dec_ref(v___y_3846_);
lean_inc(v_goal_3647_);
v___x_3857_ = l_Lean_MVarId_getType(v_goal_3647_, v___y_3855_, v___y_3843_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v_proof_3859_; lean_object* v___x_3860_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v_proof_3859_ = lean_ctor_get(v_thm_3649_, 1);
v___x_3860_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
switch(lean_obj_tag(v_proof_3859_))
{
case 0:
{
lean_object* v_declName_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v_declName_3861_ = lean_ctor_get(v_proof_3859_, 0);
v___x_3862_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3861_);
v___x_3863_ = l_Lean_MessageData_ofName(v_declName_3861_);
v___x_3864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3864_, 0, v___x_3862_);
lean_ctor_set(v___x_3864_, 1, v___x_3863_);
v___y_3799_ = v___y_3843_;
v___y_3800_ = v___y_3844_;
v___y_3801_ = v___y_3845_;
v___y_3802_ = v___y_3847_;
v___y_3803_ = v___y_3848_;
v___y_3804_ = v___y_3849_;
v___y_3805_ = v___y_3850_;
v___y_3806_ = v___y_3851_;
v___y_3807_ = v_a_3858_;
v___y_3808_ = v___y_3852_;
v___y_3809_ = v___y_3853_;
v___y_3810_ = v___y_3854_;
v___y_3811_ = v___x_3860_;
v___y_3812_ = v___y_3855_;
v___y_3813_ = v___x_3864_;
goto v___jp_3798_;
}
case 1:
{
lean_object* v_fvarId_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_fvarId_3865_ = lean_ctor_get(v_proof_3859_, 0);
v___x_3866_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3865_);
v___x_3867_ = l_Lean_mkFVar(v_fvarId_3865_);
v___x_3868_ = l_Lean_MessageData_ofExpr(v___x_3867_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3866_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
v___y_3799_ = v___y_3843_;
v___y_3800_ = v___y_3844_;
v___y_3801_ = v___y_3845_;
v___y_3802_ = v___y_3847_;
v___y_3803_ = v___y_3848_;
v___y_3804_ = v___y_3849_;
v___y_3805_ = v___y_3850_;
v___y_3806_ = v___y_3851_;
v___y_3807_ = v_a_3858_;
v___y_3808_ = v___y_3852_;
v___y_3809_ = v___y_3853_;
v___y_3810_ = v___y_3854_;
v___y_3811_ = v___x_3860_;
v___y_3812_ = v___y_3855_;
v___y_3813_ = v___x_3869_;
goto v___jp_3798_;
}
default: 
{
lean_object* v_ref_3870_; lean_object* v_proof_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
v_ref_3870_ = lean_ctor_get(v_proof_3859_, 1);
v_proof_3871_ = lean_ctor_get(v_proof_3859_, 2);
v___x_3872_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3870_);
v___x_3873_ = l_Lean_MessageData_ofSyntax(v_ref_3870_);
v___x_3874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
v___x_3875_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3874_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
lean_inc_ref(v_proof_3871_);
v___x_3877_ = l_Lean_MessageData_ofExpr(v_proof_3871_);
v___x_3878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___y_3799_ = v___y_3843_;
v___y_3800_ = v___y_3844_;
v___y_3801_ = v___y_3845_;
v___y_3802_ = v___y_3847_;
v___y_3803_ = v___y_3848_;
v___y_3804_ = v___y_3849_;
v___y_3805_ = v___y_3850_;
v___y_3806_ = v___y_3851_;
v___y_3807_ = v_a_3858_;
v___y_3808_ = v___y_3852_;
v___y_3809_ = v___y_3853_;
v___y_3810_ = v___y_3854_;
v___y_3811_ = v___x_3860_;
v___y_3812_ = v___y_3855_;
v___y_3813_ = v___x_3878_;
goto v___jp_3798_;
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v___y_3851_);
lean_dec_ref(v_thm_3649_);
lean_dec_ref(v_info_3648_);
lean_dec(v_goal_3647_);
lean_dec_ref(v_scope_3646_);
v_a_3879_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3857_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3857_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
lean_dec_ref(v___y_3851_);
v___y_3699_ = v___y_3850_;
v___y_3700_ = v___y_3843_;
v___y_3701_ = v___y_3844_;
v___y_3702_ = v___y_3852_;
v___y_3703_ = v___y_3853_;
v___y_3704_ = v___y_3854_;
v___y_3705_ = v___y_3845_;
v___y_3706_ = v___y_3855_;
v___y_3707_ = v___y_3847_;
v___y_3708_ = v___y_3848_;
v___y_3709_ = v___y_3849_;
v___y_3710_ = v___y_3846_;
goto v___jp_3698_;
}
}
v___jp_3887_:
{
lean_object* v___x_3899_; 
lean_inc_ref(v_info_3648_);
lean_inc_ref(v_thm_3649_);
v___x_3899_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_thm_3649_, v_info_3648_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
if (lean_obj_tag(v___x_3899_) == 0)
{
v___y_3699_ = v___y_3888_;
v___y_3700_ = v___y_3896_;
v___y_3701_ = v___y_3892_;
v___y_3702_ = v___y_3891_;
v___y_3703_ = v___y_3889_;
v___y_3704_ = v___y_3894_;
v___y_3705_ = v___y_3893_;
v___y_3706_ = v___y_3895_;
v___y_3707_ = v___y_3890_;
v___y_3708_ = v___y_3897_;
v___y_3709_ = v___y_3898_;
v___y_3710_ = v___x_3899_;
goto v___jp_3698_;
}
else
{
lean_object* v_a_3900_; uint8_t v___x_3901_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
v___x_3901_ = l_Lean_Exception_isInterrupt(v_a_3900_);
if (v___x_3901_ == 0)
{
uint8_t v___x_3902_; 
lean_inc(v_a_3900_);
v___x_3902_ = l_Lean_Exception_isRuntime(v_a_3900_);
v___y_3843_ = v___y_3896_;
v___y_3844_ = v___y_3892_;
v___y_3845_ = v___y_3893_;
v___y_3846_ = v___x_3899_;
v___y_3847_ = v___y_3890_;
v___y_3848_ = v___y_3897_;
v___y_3849_ = v___y_3898_;
v___y_3850_ = v___y_3888_;
v___y_3851_ = v_a_3900_;
v___y_3852_ = v___y_3891_;
v___y_3853_ = v___y_3889_;
v___y_3854_ = v___y_3894_;
v___y_3855_ = v___y_3895_;
v___y_3856_ = v___x_3902_;
goto v___jp_3842_;
}
else
{
v___y_3843_ = v___y_3896_;
v___y_3844_ = v___y_3892_;
v___y_3845_ = v___y_3893_;
v___y_3846_ = v___x_3899_;
v___y_3847_ = v___y_3890_;
v___y_3848_ = v___y_3897_;
v___y_3849_ = v___y_3898_;
v___y_3850_ = v___y_3888_;
v___y_3851_ = v_a_3900_;
v___y_3852_ = v___y_3891_;
v___y_3853_ = v___y_3889_;
v___y_3854_ = v___y_3894_;
v___y_3855_ = v___y_3895_;
v___y_3856_ = v___x_3901_;
goto v___jp_3842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object* v_scope_3954_, lean_object* v_goal_3955_, lean_object* v_info_3956_, lean_object* v_thm_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_){
_start:
{
lean_object* v_res_3970_; 
v_res_3970_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_3954_, v_goal_3955_, v_info_3956_, v_thm_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_, v_a_3968_);
lean_dec(v_a_3968_);
lean_dec_ref(v_a_3967_);
lean_dec(v_a_3966_);
lean_dec_ref(v_a_3965_);
lean_dec(v_a_3964_);
lean_dec_ref(v_a_3963_);
lean_dec(v_a_3962_);
lean_dec_ref(v_a_3961_);
lean_dec(v_a_3960_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
return v_res_3970_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_3973_ = l_Lean_stringToMessageData(v___x_3972_);
return v___x_3973_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_3976_ = l_Lean_stringToMessageData(v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_untilPat_x3f_3986_; 
v_untilPat_x3f_3986_ = lean_ctor_get(v_a_3978_, 5);
if (lean_obj_tag(v_untilPat_x3f_3986_) == 1)
{
lean_object* v_val_3987_; uint8_t v___x_3988_; lean_object* v___x_3989_; 
v_val_3987_ = lean_ctor_get(v_untilPat_x3f_3986_, 0);
v___x_3988_ = 1;
lean_inc_ref(v_prog_3977_);
lean_inc(v_val_3987_);
v___x_3989_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_3987_, v_prog_3977_, v___x_3988_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4036_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_3992_ = v___x_3989_;
v_isShared_3993_ = v_isSharedCheck_4036_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4036_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
if (lean_obj_tag(v_a_3990_) == 0)
{
uint8_t v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
lean_dec_ref(v_prog_3977_);
v___x_3994_ = 0;
v___x_3995_ = lean_box(v___x_3994_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_3995_);
v___x_3997_ = v___x_3992_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3995_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
else
{
lean_object* v_options_3999_; uint8_t v_hasTrace_4000_; 
lean_dec_ref_known(v_a_3990_, 1);
v_options_3999_ = lean_ctor_get(v_a_3983_, 2);
v_hasTrace_4000_ = lean_ctor_get_uint8(v_options_3999_, sizeof(void*)*1);
if (v_hasTrace_4000_ == 0)
{
lean_object* v___x_4001_; lean_object* v___x_4003_; 
lean_dec_ref(v_prog_3977_);
v___x_4001_ = lean_box(v___x_3988_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4001_);
v___x_4003_ = v___x_3992_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v___x_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; uint8_t v___x_4008_; 
v_inheritedTraceOptions_4005_ = lean_ctor_get(v_a_3983_, 13);
v___x_4006_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4008_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4005_, v_options_3999_, v___x_4007_);
if (v___x_4008_ == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4011_; 
lean_dec_ref(v_prog_3977_);
v___x_4009_ = lean_box(v___x_3988_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4009_);
v___x_4011_ = v___x_3992_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v___x_4009_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
else
{
lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
lean_del_object(v___x_3992_);
v___x_4013_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4014_ = l_Lean_MessageData_ofExpr(v_prog_3977_);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
v___x_4018_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4006_, v___x_4017_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4026_; 
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v___x_4018_, 0);
lean_dec(v_unused_4027_);
v___x_4020_ = v___x_4018_;
v_isShared_4021_ = v_isSharedCheck_4026_;
goto v_resetjp_4019_;
}
else
{
lean_dec(v___x_4018_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4026_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4022_; lean_object* v___x_4024_; 
v___x_4022_ = lean_box(v___x_3988_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4022_);
v___x_4024_ = v___x_4020_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v___x_4022_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
v_a_4028_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4018_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4018_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v___x_4033_; 
if (v_isShared_4031_ == 0)
{
v___x_4033_ = v___x_4030_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
return v___x_4033_;
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
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec_ref(v_prog_3977_);
v_a_4037_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_3989_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_3989_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec_ref(v_prog_3977_);
v___x_4045_ = 0;
v___x_4046_ = lean_box(v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_prog_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec_ref(v_a_4049_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object* v_prog_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_, lean_object* v_a_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v___x_4071_; 
v___x_4071_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_prog_4058_, v_a_4059_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_);
return v___x_4071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_, lean_object* v_a_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_, lean_object* v_a_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v_prog_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_, v_a_4081_, v_a_4082_, v_a_4083_);
lean_dec(v_a_4083_);
lean_dec_ref(v_a_4082_);
lean_dec(v_a_4081_);
lean_dec_ref(v_a_4080_);
lean_dec(v_a_4079_);
lean_dec_ref(v_a_4078_);
lean_dec(v_a_4077_);
lean_dec_ref(v_a_4076_);
lean_dec(v_a_4075_);
lean_dec(v_a_4074_);
lean_dec_ref(v_a_4073_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v_b_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v___x_4100_; 
lean_inc(v___y_4098_);
lean_inc_ref(v___y_4097_);
lean_inc(v___y_4096_);
lean_inc_ref(v___y_4095_);
lean_inc(v___y_4093_);
lean_inc_ref(v___y_4092_);
lean_inc(v___y_4091_);
lean_inc_ref(v___y_4090_);
lean_inc(v___y_4089_);
lean_inc(v___y_4088_);
lean_inc_ref(v___y_4087_);
v___x_4100_ = lean_apply_13(v_k_4086_, v_b_4094_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, lean_box(0));
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v_b_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v_b_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4116_, lean_object* v_type_4117_, lean_object* v_val_4118_, lean_object* v_k_4119_, uint8_t v_nondep_4120_, uint8_t v_kind_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v___f_4134_; lean_object* v___x_4135_; 
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
lean_inc(v___y_4124_);
lean_inc(v___y_4123_);
lean_inc_ref(v___y_4122_);
v___f_4134_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4134_, 0, v_k_4119_);
lean_closure_set(v___f_4134_, 1, v___y_4122_);
lean_closure_set(v___f_4134_, 2, v___y_4123_);
lean_closure_set(v___f_4134_, 3, v___y_4124_);
lean_closure_set(v___f_4134_, 4, v___y_4125_);
lean_closure_set(v___f_4134_, 5, v___y_4126_);
lean_closure_set(v___f_4134_, 6, v___y_4127_);
lean_closure_set(v___f_4134_, 7, v___y_4128_);
v___x_4135_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4116_, v_type_4117_, v_val_4118_, v___f_4134_, v_nondep_4120_, v_kind_4121_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4135_) == 0)
{
return v___x_4135_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4135_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4135_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4144_ = _args[0];
lean_object* v_type_4145_ = _args[1];
lean_object* v_val_4146_ = _args[2];
lean_object* v_k_4147_ = _args[3];
lean_object* v_nondep_4148_ = _args[4];
lean_object* v_kind_4149_ = _args[5];
lean_object* v___y_4150_ = _args[6];
lean_object* v___y_4151_ = _args[7];
lean_object* v___y_4152_ = _args[8];
lean_object* v___y_4153_ = _args[9];
lean_object* v___y_4154_ = _args[10];
lean_object* v___y_4155_ = _args[11];
lean_object* v___y_4156_ = _args[12];
lean_object* v___y_4157_ = _args[13];
lean_object* v___y_4158_ = _args[14];
lean_object* v___y_4159_ = _args[15];
lean_object* v___y_4160_ = _args[16];
lean_object* v___y_4161_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4162_; uint8_t v_kind_boxed_4163_; lean_object* v_res_4164_; 
v_nondep_boxed_4162_ = lean_unbox(v_nondep_4148_);
v_kind_boxed_4163_ = lean_unbox(v_kind_4149_);
v_res_4164_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4144_, v_type_4145_, v_val_4146_, v_k_4147_, v_nondep_boxed_4162_, v_kind_boxed_4163_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
lean_dec_ref(v___y_4155_);
lean_dec(v___y_4154_);
lean_dec_ref(v___y_4153_);
lean_dec(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4165_, lean_object* v_name_4166_, lean_object* v_type_4167_, lean_object* v_val_4168_, lean_object* v_k_4169_, uint8_t v_nondep_4170_, uint8_t v_kind_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v___x_4184_; 
v___x_4184_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4166_, v_type_4167_, v_val_4168_, v_k_4169_, v_nondep_4170_, v_kind_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
return v___x_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4185_ = _args[0];
lean_object* v_name_4186_ = _args[1];
lean_object* v_type_4187_ = _args[2];
lean_object* v_val_4188_ = _args[3];
lean_object* v_k_4189_ = _args[4];
lean_object* v_nondep_4190_ = _args[5];
lean_object* v_kind_4191_ = _args[6];
lean_object* v___y_4192_ = _args[7];
lean_object* v___y_4193_ = _args[8];
lean_object* v___y_4194_ = _args[9];
lean_object* v___y_4195_ = _args[10];
lean_object* v___y_4196_ = _args[11];
lean_object* v___y_4197_ = _args[12];
lean_object* v___y_4198_ = _args[13];
lean_object* v___y_4199_ = _args[14];
lean_object* v___y_4200_ = _args[15];
lean_object* v___y_4201_ = _args[16];
lean_object* v___y_4202_ = _args[17];
lean_object* v___y_4203_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4204_; uint8_t v_kind_boxed_4205_; lean_object* v_res_4206_; 
v_nondep_boxed_4204_ = lean_unbox(v_nondep_4190_);
v_kind_boxed_4205_ = lean_unbox(v_kind_4191_);
v_res_4206_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4185_, v_name_4186_, v_type_4187_, v_val_4188_, v_k_4189_, v_nondep_boxed_4204_, v_kind_boxed_4205_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4207_, lean_object* v_declInfos_4208_, lean_object* v_k_4209_, lean_object* v_fv_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4207_, v_declInfos_4208_, v_k_4209_, v_fv_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v___y_4214_);
lean_dec(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4224_, lean_object* v_k_4225_, lean_object* v_acc_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_, lean_object* v_a_4231_, lean_object* v_a_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4239_ = lean_array_get_size(v_acc_4226_);
v___x_4240_ = lean_array_get_size(v_declInfos_4224_);
v___x_4241_ = lean_nat_dec_lt(v___x_4239_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
lean_dec_ref(v_declInfos_4224_);
lean_inc(v_a_4237_);
lean_inc_ref(v_a_4236_);
lean_inc(v_a_4235_);
lean_inc_ref(v_a_4234_);
lean_inc(v_a_4233_);
lean_inc_ref(v_a_4232_);
lean_inc(v_a_4231_);
lean_inc_ref(v_a_4230_);
lean_inc(v_a_4229_);
lean_inc(v_a_4228_);
lean_inc_ref(v_a_4227_);
v___x_4242_ = lean_apply_13(v_k_4225_, v_acc_4226_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, lean_box(0));
return v___x_4242_;
}
else
{
lean_object* v___x_4243_; lean_object* v_snd_4244_; lean_object* v_fst_4245_; lean_object* v_fst_4246_; lean_object* v_snd_4247_; lean_object* v___f_4248_; uint8_t v___x_4249_; uint8_t v___x_4250_; lean_object* v___x_4251_; 
v___x_4243_ = lean_array_fget_borrowed(v_declInfos_4224_, v___x_4239_);
v_snd_4244_ = lean_ctor_get(v___x_4243_, 1);
v_fst_4245_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_fst_4245_);
v_fst_4246_ = lean_ctor_get(v_snd_4244_, 0);
lean_inc(v_fst_4246_);
v_snd_4247_ = lean_ctor_get(v_snd_4244_, 1);
lean_inc(v_snd_4247_);
v___f_4248_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4248_, 0, v_acc_4226_);
lean_closure_set(v___f_4248_, 1, v_declInfos_4224_);
lean_closure_set(v___f_4248_, 2, v_k_4225_);
v___x_4249_ = 0;
v___x_4250_ = 0;
v___x_4251_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4245_, v_fst_4246_, v_snd_4247_, v___f_4248_, v___x_4249_, v___x_4250_, v_a_4227_, v_a_4228_, v_a_4229_, v_a_4230_, v_a_4231_, v_a_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
return v___x_4251_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4252_, lean_object* v_declInfos_4253_, lean_object* v_k_4254_, lean_object* v_fv_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = lean_array_push(v_acc_4252_, v_fv_4255_);
v___x_4269_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4253_, v_k_4254_, v___x_4268_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4270_, lean_object* v_k_4271_, lean_object* v_acc_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4270_, v_k_4271_, v_acc_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
lean_dec(v_a_4283_);
lean_dec_ref(v_a_4282_);
lean_dec(v_a_4281_);
lean_dec_ref(v_a_4280_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
lean_dec(v_a_4275_);
lean_dec(v_a_4274_);
lean_dec_ref(v_a_4273_);
return v_res_4285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4286_, lean_object* v_h__1_4287_){
_start:
{
lean_object* v_snd_4288_; lean_object* v_fst_4289_; lean_object* v_fst_4290_; lean_object* v_snd_4291_; lean_object* v___x_4292_; 
v_snd_4288_ = lean_ctor_get(v_x_4286_, 1);
lean_inc(v_snd_4288_);
v_fst_4289_ = lean_ctor_get(v_x_4286_, 0);
lean_inc(v_fst_4289_);
lean_dec_ref(v_x_4286_);
v_fst_4290_ = lean_ctor_get(v_snd_4288_, 0);
lean_inc(v_fst_4290_);
v_snd_4291_ = lean_ctor_get(v_snd_4288_, 1);
lean_inc(v_snd_4291_);
lean_dec(v_snd_4288_);
v___x_4292_ = lean_apply_3(v_h__1_4287_, v_fst_4289_, v_fst_4290_, v_snd_4291_);
return v___x_4292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4293_, lean_object* v_x_4294_, lean_object* v_h__1_4295_){
_start:
{
lean_object* v_snd_4296_; lean_object* v_fst_4297_; lean_object* v_fst_4298_; lean_object* v_snd_4299_; lean_object* v___x_4300_; 
v_snd_4296_ = lean_ctor_get(v_x_4294_, 1);
lean_inc(v_snd_4296_);
v_fst_4297_ = lean_ctor_get(v_x_4294_, 0);
lean_inc(v_fst_4297_);
lean_dec_ref(v_x_4294_);
v_fst_4298_ = lean_ctor_get(v_snd_4296_, 0);
lean_inc(v_fst_4298_);
v_snd_4299_ = lean_ctor_get(v_snd_4296_, 1);
lean_inc(v_snd_4299_);
lean_dec(v_snd_4296_);
v___x_4300_ = lean_apply_3(v_h__1_4295_, v_fst_4297_, v_fst_4298_, v_snd_4299_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(lean_object* v_declInfos_4303_, lean_object* v_k_4304_, lean_object* v_a_4305_, lean_object* v_a_4306_, lean_object* v_a_4307_, lean_object* v_a_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v___x_4317_; lean_object* v___x_4318_; 
v___x_4317_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0));
v___x_4318_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4303_, v_k_4304_, v___x_4317_, v_a_4305_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4319_, lean_object* v_k_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_){
_start:
{
lean_object* v_res_4333_; 
v_res_4333_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(v_declInfos_4319_, v_k_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_);
lean_dec(v_a_4331_);
lean_dec_ref(v_a_4330_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec(v_a_4322_);
lean_dec_ref(v_a_4321_);
return v_res_4333_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object* v_x_4334_){
_start:
{
uint8_t v___x_4335_; 
v___x_4335_ = 0;
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4336_){
_start:
{
uint8_t v_res_4337_; lean_object* v_r_4338_; 
v_res_4337_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(v_x_4336_);
lean_dec(v_x_4336_);
v_r_4338_ = lean_box(v_res_4337_);
return v_r_4338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4339_, lean_object* v___x_4340_, uint8_t v___x_4341_, lean_object* v___x_4342_, lean_object* v_fvs_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v___x_4351_; 
v___x_4351_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4339_, v___x_4340_, v___x_4341_, v___x_4341_, v___x_4342_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; uint8_t v___x_4353_; lean_object* v___x_4354_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = 0;
v___x_4354_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4353_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
if (lean_obj_tag(v___x_4354_) == 0)
{
uint8_t v___x_4355_; lean_object* v___x_4356_; 
lean_dec_ref_known(v___x_4354_, 1);
v___x_4355_ = 1;
v___x_4356_ = l_Lean_Meta_mkLetFVars(v_fvs_4343_, v_a_4352_, v___x_4341_, v___x_4341_, v___x_4355_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
return v___x_4356_;
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec(v_a_4352_);
v_a_4357_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4354_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4354_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
return v___x_4351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4365_, lean_object* v___x_4366_, lean_object* v___x_4367_, lean_object* v___x_4368_, lean_object* v_fvs_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
uint8_t v___x_11349__boxed_4377_; lean_object* v_res_4378_; 
v___x_11349__boxed_4377_ = lean_unbox(v___x_4367_);
v_res_4378_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(v_frameStx_4365_, v___x_4366_, v___x_11349__boxed_4377_, v___x_4368_, v_fvs_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec_ref(v___y_4370_);
lean_dec_ref(v_fvs_4369_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4384_, lean_object* v_frameStx_4385_, lean_object* v___f_4386_, lean_object* v_fvs_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; uint8_t v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___f_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; uint8_t v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; 
v___x_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_resourceTy_4384_);
v___x_4401_ = 1;
v___x_4402_ = lean_box(0);
v___x_4403_ = lean_box(v___x_4401_);
v___f_4404_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4404_, 0, v_frameStx_4385_);
lean_closure_set(v___f_4404_, 1, v___x_4400_);
lean_closure_set(v___f_4404_, 2, v___x_4403_);
lean_closure_set(v___f_4404_, 3, v___x_4402_);
lean_closure_set(v___f_4404_, 4, v_fvs_4387_);
v___x_4405_ = lean_box(0);
v___x_4406_ = lean_box(1);
v___x_4407_ = 0;
v___x_4408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0));
v___x_4409_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4409_, 0, v___x_4402_);
lean_ctor_set(v___x_4409_, 1, v___x_4405_);
lean_ctor_set(v___x_4409_, 2, v___x_4402_);
lean_ctor_set(v___x_4409_, 3, v___f_4386_);
lean_ctor_set(v___x_4409_, 4, v___x_4406_);
lean_ctor_set(v___x_4409_, 5, v___x_4406_);
lean_ctor_set(v___x_4409_, 6, v___x_4402_);
lean_ctor_set(v___x_4409_, 7, v___x_4408_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8, v___x_4401_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 1, v___x_4401_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 2, v___x_4401_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 3, v___x_4401_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 4, v___x_4407_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 5, v___x_4407_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 6, v___x_4407_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 7, v___x_4407_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 8, v___x_4401_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 9, v___x_4407_);
lean_ctor_set_uint8(v___x_4409_, sizeof(void*)*8 + 10, v___x_4401_);
v___x_4410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1));
v___x_4411_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4404_, v___x_4409_, v___x_4410_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v_fst_4413_; lean_object* v___x_4414_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v_fst_4413_ = lean_ctor_get(v_a_4412_, 0);
lean_inc(v_fst_4413_);
lean_dec(v_a_4412_);
v___x_4414_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4413_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4414_;
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
v_a_4415_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4411_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4411_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_4423_, lean_object* v_frameStx_4424_, lean_object* v___f_4425_, lean_object* v_fvs_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(v_resourceTy_4423_, v_frameStx_4424_, v___f_4425_, v_fvs_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
lean_dec(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object* v___x_4440_, lean_object* v_res_4441_, lean_object* v_range_4442_, lean_object* v_b_4443_, lean_object* v_i_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_){
_start:
{
lean_object* v_stop_4450_; lean_object* v_step_4451_; lean_object* v_a_4453_; uint8_t v___x_4456_; 
v_stop_4450_ = lean_ctor_get(v_range_4442_, 1);
v_step_4451_ = lean_ctor_get(v_range_4442_, 2);
v___x_4456_ = lean_nat_dec_lt(v_i_4444_, v_stop_4450_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; 
lean_dec(v_i_4444_);
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v_b_4443_);
return v___x_4457_;
}
else
{
lean_object* v___x_4458_; 
v___x_4458_ = lean_array_fget_borrowed(v___x_4440_, v_i_4444_);
if (lean_obj_tag(v___x_4458_) == 1)
{
lean_object* v_val_4459_; lean_object* v_args_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v_val_4459_ = lean_ctor_get(v___x_4458_, 0);
v_args_4460_ = lean_ctor_get(v_res_4441_, 1);
v___x_4461_ = lean_array_get_size(v_args_4460_);
v___x_4462_ = lean_nat_dec_lt(v_i_4444_, v___x_4461_);
if (v___x_4462_ == 0)
{
v_a_4453_ = v_b_4443_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; 
v___x_4463_ = l_Lean_instInhabitedExpr;
v___x_4464_ = lean_array_get_borrowed(v___x_4463_, v_args_4460_, v_i_4444_);
lean_inc(v___y_4448_);
lean_inc_ref(v___y_4447_);
lean_inc(v___y_4446_);
lean_inc_ref(v___y_4445_);
lean_inc(v___x_4464_);
v___x_4465_ = lean_infer_type(v___x_4464_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_object* v_a_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
lean_inc(v___x_4464_);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v_a_4466_);
lean_ctor_set(v___x_4467_, 1, v___x_4464_);
lean_inc(v_val_4459_);
v___x_4468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4468_, 0, v_val_4459_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = lean_array_push(v_b_4443_, v___x_4468_);
v_a_4453_ = v___x_4469_;
goto v___jp_4452_;
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_i_4444_);
lean_dec_ref(v_b_4443_);
v_a_4470_ = lean_ctor_get(v___x_4465_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4465_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4465_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4465_);
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
v_a_4453_ = v_b_4443_;
goto v___jp_4452_;
}
}
v___jp_4452_:
{
lean_object* v___x_4454_; 
v___x_4454_ = lean_nat_add(v_i_4444_, v_step_4451_);
lean_dec(v_i_4444_);
v_b_4443_ = v_a_4453_;
v_i_4444_ = v___x_4454_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v___x_4478_, lean_object* v_res_4479_, lean_object* v_range_4480_, lean_object* v_b_4481_, lean_object* v_i_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v___x_4478_, v_res_4479_, v_range_4480_, v_b_4481_, v_i_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec_ref(v_range_4480_);
lean_dec_ref(v_res_4479_);
lean_dec_ref(v___x_4478_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object* v_resourceTy_4492_, lean_object* v_entry_4493_, lean_object* v_res_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_varNames_4507_; lean_object* v_frameStx_4508_; lean_object* v___x_4509_; lean_object* v_decls_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; 
v_varNames_4507_ = lean_ctor_get(v_entry_4493_, 1);
lean_inc_ref(v_varNames_4507_);
v_frameStx_4508_ = lean_ctor_get(v_entry_4493_, 2);
lean_inc(v_frameStx_4508_);
lean_dec_ref(v_entry_4493_);
v___x_4509_ = lean_unsigned_to_nat(0u);
v_decls_4510_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0));
v___x_4511_ = lean_array_get_size(v_varNames_4507_);
v___x_4512_ = lean_unsigned_to_nat(1u);
v___x_4513_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4509_);
lean_ctor_set(v___x_4513_, 1, v___x_4511_);
lean_ctor_set(v___x_4513_, 2, v___x_4512_);
v___x_4514_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_varNames_4507_, v_res_4494_, v___x_4513_, v_decls_4510_, v___x_4509_, v_a_4502_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec_ref_known(v___x_4513_, 3);
lean_dec_ref(v_varNames_4507_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v_keyedConfig_4516_; uint8_t v_trackZetaDelta_4517_; lean_object* v_zetaDeltaSet_4518_; lean_object* v_lctx_4519_; lean_object* v_localInstances_4520_; lean_object* v_defEqCtx_x3f_4521_; lean_object* v_synthPendingDepth_4522_; lean_object* v_customCanUnfoldPredicate_x3f_4523_; uint8_t v_univApprox_4524_; uint8_t v_inTypeClassResolution_4525_; uint8_t v_cacheInferType_4526_; lean_object* v___f_4527_; lean_object* v___f_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v_keyedConfig_4516_ = lean_ctor_get(v_a_4502_, 0);
v_trackZetaDelta_4517_ = lean_ctor_get_uint8(v_a_4502_, sizeof(void*)*7);
v_zetaDeltaSet_4518_ = lean_ctor_get(v_a_4502_, 1);
v_lctx_4519_ = lean_ctor_get(v_a_4502_, 2);
v_localInstances_4520_ = lean_ctor_get(v_a_4502_, 3);
v_defEqCtx_x3f_4521_ = lean_ctor_get(v_a_4502_, 4);
v_synthPendingDepth_4522_ = lean_ctor_get(v_a_4502_, 5);
v_customCanUnfoldPredicate_x3f_4523_ = lean_ctor_get(v_a_4502_, 6);
v_univApprox_4524_ = lean_ctor_get_uint8(v_a_4502_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4525_ = lean_ctor_get_uint8(v_a_4502_, sizeof(void*)*7 + 2);
v_cacheInferType_4526_ = lean_ctor_get_uint8(v_a_4502_, sizeof(void*)*7 + 3);
v___f_4527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1));
v___f_4528_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4528_, 0, v_resourceTy_4492_);
lean_closure_set(v___f_4528_, 1, v_frameStx_4508_);
lean_closure_set(v___f_4528_, 2, v___f_4527_);
v___x_4529_ = 1;
lean_inc_ref(v_keyedConfig_4516_);
v___x_4530_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4529_, v_keyedConfig_4516_);
lean_inc(v_customCanUnfoldPredicate_x3f_4523_);
lean_inc(v_synthPendingDepth_4522_);
lean_inc(v_defEqCtx_x3f_4521_);
lean_inc_ref(v_localInstances_4520_);
lean_inc_ref(v_lctx_4519_);
lean_inc(v_zetaDeltaSet_4518_);
v___x_4531_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
lean_ctor_set(v___x_4531_, 1, v_zetaDeltaSet_4518_);
lean_ctor_set(v___x_4531_, 2, v_lctx_4519_);
lean_ctor_set(v___x_4531_, 3, v_localInstances_4520_);
lean_ctor_set(v___x_4531_, 4, v_defEqCtx_x3f_4521_);
lean_ctor_set(v___x_4531_, 5, v_synthPendingDepth_4522_);
lean_ctor_set(v___x_4531_, 6, v_customCanUnfoldPredicate_x3f_4523_);
lean_ctor_set_uint8(v___x_4531_, sizeof(void*)*7, v_trackZetaDelta_4517_);
lean_ctor_set_uint8(v___x_4531_, sizeof(void*)*7 + 1, v_univApprox_4524_);
lean_ctor_set_uint8(v___x_4531_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4525_);
lean_ctor_set_uint8(v___x_4531_, sizeof(void*)*7 + 3, v_cacheInferType_4526_);
v___x_4532_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_a_4515_, v___f_4528_, v_decls_4510_, v_a_4495_, v_a_4496_, v_a_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_, v___x_4531_, v_a_4503_, v_a_4504_, v_a_4505_);
lean_dec_ref_known(v___x_4531_, 7);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4540_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4540_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4538_; 
if (v_isShared_4536_ == 0)
{
v___x_4538_ = v___x_4535_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_a_4533_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
else
{
return v___x_4532_;
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
lean_dec(v_frameStx_4508_);
lean_dec_ref(v_resourceTy_4492_);
v_a_4541_ = lean_ctor_get(v___x_4514_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4514_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4514_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4514_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object* v_resourceTy_4549_, lean_object* v_entry_4550_, lean_object* v_res_4551_, lean_object* v_a_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_resourceTy_4549_, v_entry_4550_, v_res_4551_, v_a_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec_ref(v_a_4559_);
lean_dec(v_a_4558_);
lean_dec_ref(v_a_4557_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec(v_a_4553_);
lean_dec_ref(v_a_4552_);
lean_dec_ref(v_res_4551_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object* v___x_4565_, lean_object* v_res_4566_, lean_object* v_range_4567_, lean_object* v_b_4568_, lean_object* v_i_4569_, lean_object* v_hs_4570_, lean_object* v_hl_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v___x_4565_, v_res_4566_, v_range_4567_, v_b_4568_, v_i_4569_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
return v___x_4584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object** _args){
lean_object* v___x_4585_ = _args[0];
lean_object* v_res_4586_ = _args[1];
lean_object* v_range_4587_ = _args[2];
lean_object* v_b_4588_ = _args[3];
lean_object* v_i_4589_ = _args[4];
lean_object* v_hs_4590_ = _args[5];
lean_object* v_hl_4591_ = _args[6];
lean_object* v___y_4592_ = _args[7];
lean_object* v___y_4593_ = _args[8];
lean_object* v___y_4594_ = _args[9];
lean_object* v___y_4595_ = _args[10];
lean_object* v___y_4596_ = _args[11];
lean_object* v___y_4597_ = _args[12];
lean_object* v___y_4598_ = _args[13];
lean_object* v___y_4599_ = _args[14];
lean_object* v___y_4600_ = _args[15];
lean_object* v___y_4601_ = _args[16];
lean_object* v___y_4602_ = _args[17];
lean_object* v___y_4603_ = _args[18];
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(v___x_4585_, v_res_4586_, v_range_4587_, v_b_4588_, v_i_4589_, v_hs_4590_, v_hl_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
lean_dec(v___y_4602_);
lean_dec_ref(v___y_4601_);
lean_dec(v___y_4600_);
lean_dec_ref(v___y_4599_);
lean_dec(v___y_4598_);
lean_dec_ref(v___y_4597_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
lean_dec_ref(v_range_4587_);
lean_dec_ref(v_res_4586_);
lean_dec_ref(v___x_4585_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_4605_, lean_object* v___x_4606_, lean_object* v_as_4607_, size_t v_sz_4608_, size_t v_i_4609_, lean_object* v_b_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v_a_4619_; uint8_t v___x_4623_; 
v___x_4623_ = lean_usize_dec_lt(v_i_4609_, v_sz_4608_);
if (v___x_4623_ == 0)
{
lean_object* v___x_4624_; 
lean_dec_ref(v___x_4606_);
v___x_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4624_, 0, v_b_4610_);
return v___x_4624_;
}
else
{
lean_object* v_entries_4625_; lean_object* v___x_4626_; lean_object* v_a_4627_; lean_object* v___x_4628_; uint8_t v_retired_4629_; 
v_entries_4625_ = lean_ctor_get(v___x_4605_, 1);
v___x_4626_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
v_a_4627_ = lean_array_uget_borrowed(v_as_4607_, v_i_4609_);
v___x_4628_ = lean_array_get_borrowed(v___x_4626_, v_entries_4625_, v_a_4627_);
v_retired_4629_ = lean_ctor_get_uint8(v___x_4628_, sizeof(void*)*4);
if (v_retired_4629_ == 0)
{
lean_object* v_pat_4630_; lean_object* v_srcIdx_4631_; lean_object* v___x_4632_; 
v_pat_4630_ = lean_ctor_get(v___x_4628_, 0);
v_srcIdx_4631_ = lean_ctor_get(v___x_4628_, 3);
lean_inc_ref(v___x_4606_);
lean_inc_ref(v_pat_4630_);
v___x_4632_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4630_, v___x_4606_, v___x_4623_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
if (lean_obj_tag(v___x_4632_) == 0)
{
lean_object* v_a_4633_; 
v_a_4633_ = lean_ctor_get(v___x_4632_, 0);
lean_inc(v_a_4633_);
lean_dec_ref_known(v___x_4632_, 1);
if (lean_obj_tag(v_a_4633_) == 1)
{
if (lean_obj_tag(v_b_4610_) == 0)
{
lean_object* v_val_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4642_; 
v_val_4634_ = lean_ctor_get(v_a_4633_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v_a_4633_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4636_ = v_a_4633_;
v_isShared_4637_ = v_isSharedCheck_4642_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_val_4634_);
lean_dec(v_a_4633_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4642_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; lean_object* v___x_4640_; 
lean_inc(v___x_4628_);
v___x_4638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4628_);
lean_ctor_set(v___x_4638_, 1, v_val_4634_);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 0, v___x_4638_);
v___x_4640_ = v___x_4636_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
v_a_4619_ = v___x_4640_;
goto v___jp_4618_;
}
}
}
else
{
lean_object* v_val_4643_; lean_object* v_fst_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4662_; 
v_val_4643_ = lean_ctor_get(v_b_4610_, 0);
lean_inc(v_val_4643_);
v_fst_4644_ = lean_ctor_get(v_val_4643_, 0);
v_isSharedCheck_4662_ = !lean_is_exclusive(v_val_4643_);
if (v_isSharedCheck_4662_ == 0)
{
lean_object* v_unused_4663_; 
v_unused_4663_ = lean_ctor_get(v_val_4643_, 1);
lean_dec(v_unused_4663_);
v___x_4646_ = v_val_4643_;
v_isShared_4647_ = v_isSharedCheck_4662_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_fst_4644_);
lean_dec(v_val_4643_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4662_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v_val_4648_; lean_object* v_srcIdx_4649_; uint8_t v___x_4650_; 
v_val_4648_ = lean_ctor_get(v_a_4633_, 0);
lean_inc(v_val_4648_);
lean_dec_ref_known(v_a_4633_, 1);
v_srcIdx_4649_ = lean_ctor_get(v_fst_4644_, 3);
lean_inc(v_srcIdx_4649_);
lean_dec(v_fst_4644_);
v___x_4650_ = lean_nat_dec_lt(v_srcIdx_4631_, v_srcIdx_4649_);
lean_dec(v_srcIdx_4649_);
if (v___x_4650_ == 0)
{
lean_dec(v_val_4648_);
lean_del_object(v___x_4646_);
v_a_4619_ = v_b_4610_;
goto v___jp_4618_;
}
else
{
lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4660_; 
v_isSharedCheck_4660_ = !lean_is_exclusive(v_b_4610_);
if (v_isSharedCheck_4660_ == 0)
{
lean_object* v_unused_4661_; 
v_unused_4661_ = lean_ctor_get(v_b_4610_, 0);
lean_dec(v_unused_4661_);
v___x_4652_ = v_b_4610_;
v_isShared_4653_ = v_isSharedCheck_4660_;
goto v_resetjp_4651_;
}
else
{
lean_dec(v_b_4610_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4660_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
lean_inc(v___x_4628_);
if (v_isShared_4647_ == 0)
{
lean_ctor_set(v___x_4646_, 1, v_val_4648_);
lean_ctor_set(v___x_4646_, 0, v___x_4628_);
v___x_4655_ = v___x_4646_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4659_; 
v_reuseFailAlloc_4659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4659_, 0, v___x_4628_);
lean_ctor_set(v_reuseFailAlloc_4659_, 1, v_val_4648_);
v___x_4655_ = v_reuseFailAlloc_4659_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
lean_object* v___x_4657_; 
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4655_);
v___x_4657_ = v___x_4652_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
v_a_4619_ = v___x_4657_;
goto v___jp_4618_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4633_);
v_a_4619_ = v_b_4610_;
goto v___jp_4618_;
}
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_dec(v_b_4610_);
lean_dec_ref(v___x_4606_);
v_a_4664_ = lean_ctor_get(v___x_4632_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4632_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4632_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4632_);
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
v_a_4619_ = v_b_4610_;
goto v___jp_4618_;
}
}
v___jp_4618_:
{
size_t v___x_4620_; size_t v___x_4621_; 
v___x_4620_ = ((size_t)1ULL);
v___x_4621_ = lean_usize_add(v_i_4609_, v___x_4620_);
v_i_4609_ = v___x_4621_;
v_b_4610_ = v_a_4619_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_4672_, lean_object* v___x_4673_, lean_object* v_as_4674_, lean_object* v_sz_4675_, lean_object* v_i_4676_, lean_object* v_b_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_){
_start:
{
size_t v_sz_boxed_4685_; size_t v_i_boxed_4686_; lean_object* v_res_4687_; 
v_sz_boxed_4685_ = lean_unbox_usize(v_sz_4675_);
lean_dec(v_sz_4675_);
v_i_boxed_4686_ = lean_unbox_usize(v_i_4676_);
lean_dec(v_i_4676_);
v_res_4687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4672_, v___x_4673_, v_as_4674_, v_sz_boxed_4685_, v_i_boxed_4686_, v_b_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
lean_dec_ref(v___y_4680_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec_ref(v_as_4674_);
lean_dec_ref(v___x_4672_);
return v_res_4687_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4689_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0));
v___x_4690_ = l_Lean_stringToMessageData(v___x_4689_);
return v___x_4690_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_4692_; lean_object* v___x_4693_; 
v___x_4692_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2));
v___x_4693_ = l_Lean_stringToMessageData(v___x_4692_);
return v___x_4693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object* v_resourceTy_4694_, lean_object* v_info_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_, lean_object* v_a_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_){
_start:
{
lean_object* v___x_4708_; lean_object* v_frameDB_4709_; lean_object* v_tree_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; size_t v_sz_4714_; size_t v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4829_; 
v___x_4708_ = lean_st_ref_get(v_a_4697_);
v_frameDB_4709_ = lean_ctor_get(v___x_4708_, 4);
lean_inc_ref(v_frameDB_4709_);
lean_dec(v___x_4708_);
v_tree_4710_ = lean_ctor_get(v_frameDB_4709_, 0);
v___x_4711_ = lean_box(0);
v___x_4712_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_4695_);
v___x_4713_ = l_Lean_Meta_Sym_getMatch___redArg(v_tree_4710_, v___x_4712_);
v_sz_4714_ = lean_array_size(v___x_4713_);
v___x_4715_ = ((size_t)0ULL);
lean_inc_ref(v___x_4712_);
v___x_4716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_frameDB_4709_, v___x_4712_, v___x_4713_, v_sz_4714_, v___x_4715_, v___x_4711_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
lean_dec_ref(v___x_4713_);
v_isSharedCheck_4829_ = !lean_is_exclusive(v_frameDB_4709_);
if (v_isSharedCheck_4829_ == 0)
{
lean_object* v_unused_4830_; lean_object* v_unused_4831_; 
v_unused_4830_ = lean_ctor_get(v_frameDB_4709_, 1);
lean_dec(v_unused_4830_);
v_unused_4831_ = lean_ctor_get(v_frameDB_4709_, 0);
lean_dec(v_unused_4831_);
v___x_4718_ = v_frameDB_4709_;
v_isShared_4719_ = v_isSharedCheck_4829_;
goto v_resetjp_4717_;
}
else
{
lean_dec(v_frameDB_4709_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4829_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
if (lean_obj_tag(v___x_4716_) == 0)
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4820_; 
v_a_4720_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4722_ = v___x_4716_;
v_isShared_4723_ = v_isSharedCheck_4820_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4716_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4820_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
if (lean_obj_tag(v_a_4720_) == 1)
{
lean_object* v_val_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4816_; 
lean_del_object(v___x_4722_);
v_val_4724_ = lean_ctor_get(v_a_4720_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v_a_4720_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4726_ = v_a_4720_;
v_isShared_4727_ = v_isSharedCheck_4816_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_val_4724_);
lean_dec(v_a_4720_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4816_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v_fst_4728_; lean_object* v_snd_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4815_; 
v_fst_4728_ = lean_ctor_get(v_val_4724_, 0);
v_snd_4729_ = lean_ctor_get(v_val_4724_, 1);
v_isSharedCheck_4815_ = !lean_is_exclusive(v_val_4724_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4731_ = v_val_4724_;
v_isShared_4732_ = v_isSharedCheck_4815_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_snd_4729_);
lean_inc(v_fst_4728_);
lean_dec(v_val_4724_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4815_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4733_; lean_object* v_frameDB_4734_; lean_object* v_specBackwardRuleCache_4735_; lean_object* v_splitBackwardRuleCache_4736_; lean_object* v_latticeBackwardRuleCache_4737_; lean_object* v_frameBackwardRuleCache_4738_; lean_object* v_invariants_4739_; lean_object* v_vcs_4740_; lean_object* v_simpState_4741_; lean_object* v_fuel_4742_; lean_object* v_inlineHandledInvariants_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4814_; 
v___x_4733_ = lean_st_ref_take(v_a_4697_);
v_frameDB_4734_ = lean_ctor_get(v___x_4733_, 4);
v_specBackwardRuleCache_4735_ = lean_ctor_get(v___x_4733_, 0);
v_splitBackwardRuleCache_4736_ = lean_ctor_get(v___x_4733_, 1);
v_latticeBackwardRuleCache_4737_ = lean_ctor_get(v___x_4733_, 2);
v_frameBackwardRuleCache_4738_ = lean_ctor_get(v___x_4733_, 3);
v_invariants_4739_ = lean_ctor_get(v___x_4733_, 5);
v_vcs_4740_ = lean_ctor_get(v___x_4733_, 6);
v_simpState_4741_ = lean_ctor_get(v___x_4733_, 7);
v_fuel_4742_ = lean_ctor_get(v___x_4733_, 8);
v_inlineHandledInvariants_4743_ = lean_ctor_get(v___x_4733_, 9);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4745_ = v___x_4733_;
v_isShared_4746_ = v_isSharedCheck_4814_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_inlineHandledInvariants_4743_);
lean_inc(v_fuel_4742_);
lean_inc(v_simpState_4741_);
lean_inc(v_vcs_4740_);
lean_inc(v_invariants_4739_);
lean_inc(v_frameDB_4734_);
lean_inc(v_frameBackwardRuleCache_4738_);
lean_inc(v_latticeBackwardRuleCache_4737_);
lean_inc(v_splitBackwardRuleCache_4736_);
lean_inc(v_specBackwardRuleCache_4735_);
lean_dec(v___x_4733_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4814_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v_tree_4747_; lean_object* v_entries_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4813_; 
v_tree_4747_ = lean_ctor_get(v_frameDB_4734_, 0);
v_entries_4748_ = lean_ctor_get(v_frameDB_4734_, 1);
v_isSharedCheck_4813_ = !lean_is_exclusive(v_frameDB_4734_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4750_ = v_frameDB_4734_;
v_isShared_4751_ = v_isSharedCheck_4813_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_entries_4748_);
lean_inc(v_tree_4747_);
lean_dec(v_frameDB_4734_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4813_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v_pat_4752_; lean_object* v_varNames_4753_; lean_object* v_frameStx_4754_; lean_object* v_srcIdx_4755_; uint8_t v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v_pat_4752_ = lean_ctor_get(v_fst_4728_, 0);
v_varNames_4753_ = lean_ctor_get(v_fst_4728_, 1);
v_frameStx_4754_ = lean_ctor_get(v_fst_4728_, 2);
v_srcIdx_4755_ = lean_ctor_get(v_fst_4728_, 3);
v___x_4756_ = 1;
lean_inc(v_srcIdx_4755_);
lean_inc(v_frameStx_4754_);
lean_inc_ref(v_varNames_4753_);
lean_inc_ref(v_pat_4752_);
v___x_4757_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4757_, 0, v_pat_4752_);
lean_ctor_set(v___x_4757_, 1, v_varNames_4753_);
lean_ctor_set(v___x_4757_, 2, v_frameStx_4754_);
lean_ctor_set(v___x_4757_, 3, v_srcIdx_4755_);
lean_ctor_set_uint8(v___x_4757_, sizeof(void*)*4, v___x_4756_);
v___x_4758_ = lean_array_set(v_entries_4748_, v_srcIdx_4755_, v___x_4757_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set(v___x_4750_, 1, v___x_4758_);
v___x_4760_ = v___x_4750_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_tree_4747_);
lean_ctor_set(v_reuseFailAlloc_4812_, 1, v___x_4758_);
v___x_4760_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4762_; 
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 4, v___x_4760_);
v___x_4762_ = v___x_4745_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_specBackwardRuleCache_4735_);
lean_ctor_set(v_reuseFailAlloc_4811_, 1, v_splitBackwardRuleCache_4736_);
lean_ctor_set(v_reuseFailAlloc_4811_, 2, v_latticeBackwardRuleCache_4737_);
lean_ctor_set(v_reuseFailAlloc_4811_, 3, v_frameBackwardRuleCache_4738_);
lean_ctor_set(v_reuseFailAlloc_4811_, 4, v___x_4760_);
lean_ctor_set(v_reuseFailAlloc_4811_, 5, v_invariants_4739_);
lean_ctor_set(v_reuseFailAlloc_4811_, 6, v_vcs_4740_);
lean_ctor_set(v_reuseFailAlloc_4811_, 7, v_simpState_4741_);
lean_ctor_set(v_reuseFailAlloc_4811_, 8, v_fuel_4742_);
lean_ctor_set(v_reuseFailAlloc_4811_, 9, v_inlineHandledInvariants_4743_);
v___x_4762_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4763_ = lean_st_ref_set(v_a_4697_, v___x_4762_);
v___x_4764_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_resourceTy_4694_, v_fst_4728_, v_snd_4729_, v_a_4696_, v_a_4697_, v_a_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
lean_dec(v_snd_4729_);
if (lean_obj_tag(v___x_4764_) == 0)
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4802_; 
v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4767_ = v___x_4764_;
v_isShared_4768_ = v_isSharedCheck_4802_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4764_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4802_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v_options_4776_; uint8_t v_hasTrace_4777_; 
v_options_4776_ = lean_ctor_get(v_a_4705_, 2);
v_hasTrace_4777_ = lean_ctor_get_uint8(v_options_4776_, sizeof(void*)*1);
if (v_hasTrace_4777_ == 0)
{
lean_del_object(v___x_4731_);
lean_del_object(v___x_4718_);
lean_dec_ref(v___x_4712_);
goto v___jp_4769_;
}
else
{
lean_object* v_inheritedTraceOptions_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; uint8_t v___x_4781_; 
v_inheritedTraceOptions_4778_ = lean_ctor_get(v_a_4705_, 13);
v___x_4779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4780_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4781_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4778_, v_options_4776_, v___x_4780_);
if (v___x_4781_ == 0)
{
lean_del_object(v___x_4731_);
lean_del_object(v___x_4718_);
lean_dec_ref(v___x_4712_);
goto v___jp_4769_;
}
else
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4785_; 
v___x_4782_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1);
v___x_4783_ = l_Lean_MessageData_ofExpr(v___x_4712_);
if (v_isShared_4732_ == 0)
{
lean_ctor_set_tag(v___x_4731_, 7);
lean_ctor_set(v___x_4731_, 1, v___x_4783_);
lean_ctor_set(v___x_4731_, 0, v___x_4782_);
v___x_4785_ = v___x_4731_;
goto v_reusejp_4784_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v___x_4782_);
lean_ctor_set(v_reuseFailAlloc_4801_, 1, v___x_4783_);
v___x_4785_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4784_;
}
v_reusejp_4784_:
{
lean_object* v___x_4786_; lean_object* v___x_4788_; 
v___x_4786_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_4719_ == 0)
{
lean_ctor_set_tag(v___x_4718_, 7);
lean_ctor_set(v___x_4718_, 1, v___x_4786_);
lean_ctor_set(v___x_4718_, 0, v___x_4785_);
v___x_4788_ = v___x_4718_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v___x_4785_);
lean_ctor_set(v_reuseFailAlloc_4800_, 1, v___x_4786_);
v___x_4788_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_inc(v_a_4765_);
v___x_4789_ = l_Lean_indentExpr(v_a_4765_);
v___x_4790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4788_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4779_, v___x_4790_, v_a_4703_, v_a_4704_, v_a_4705_, v_a_4706_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_dec_ref_known(v___x_4791_, 1);
goto v___jp_4769_;
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_del_object(v___x_4767_);
lean_dec(v_a_4765_);
lean_del_object(v___x_4726_);
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4791_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4791_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
}
}
}
v___jp_4769_:
{
lean_object* v___x_4771_; 
if (v_isShared_4727_ == 0)
{
lean_ctor_set(v___x_4726_, 0, v_a_4765_);
v___x_4771_ = v___x_4726_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4775_; 
v_reuseFailAlloc_4775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4775_, 0, v_a_4765_);
v___x_4771_ = v_reuseFailAlloc_4775_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
lean_object* v___x_4773_; 
if (v_isShared_4768_ == 0)
{
lean_ctor_set(v___x_4767_, 0, v___x_4771_);
v___x_4773_ = v___x_4767_;
goto v_reusejp_4772_;
}
else
{
lean_object* v_reuseFailAlloc_4774_; 
v_reuseFailAlloc_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4771_);
v___x_4773_ = v_reuseFailAlloc_4774_;
goto v_reusejp_4772_;
}
v_reusejp_4772_:
{
return v___x_4773_;
}
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_del_object(v___x_4731_);
lean_del_object(v___x_4726_);
lean_del_object(v___x_4718_);
lean_dec_ref(v___x_4712_);
v_a_4803_ = lean_ctor_get(v___x_4764_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4764_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4764_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
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
lean_object* v___x_4818_; 
lean_dec(v_a_4720_);
lean_del_object(v___x_4718_);
lean_dec_ref(v___x_4712_);
lean_dec_ref(v_resourceTy_4694_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 0, v___x_4711_);
v___x_4818_ = v___x_4722_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4711_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_del_object(v___x_4718_);
lean_dec_ref(v___x_4712_);
lean_dec_ref(v_resourceTy_4694_);
v_a_4821_ = lean_ctor_get(v___x_4716_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4716_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4716_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4716_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4827_; 
v_reuseFailAlloc_4827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4827_, 0, v_a_4821_);
v___x_4826_ = v_reuseFailAlloc_4827_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
return v___x_4826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object* v_resourceTy_4832_, lean_object* v_info_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v_res_4846_; 
v_res_4846_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_resourceTy_4832_, v_info_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_);
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
lean_dec_ref(v_info_4833_);
return v_res_4846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_4847_, lean_object* v___x_4848_, lean_object* v_as_4849_, size_t v_sz_4850_, size_t v_i_4851_, lean_object* v_b_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v___x_4865_; 
v___x_4865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4847_, v___x_4848_, v_as_4849_, v_sz_4850_, v_i_4851_, v_b_4852_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
return v___x_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_4866_ = _args[0];
lean_object* v___x_4867_ = _args[1];
lean_object* v_as_4868_ = _args[2];
lean_object* v_sz_4869_ = _args[3];
lean_object* v_i_4870_ = _args[4];
lean_object* v_b_4871_ = _args[5];
lean_object* v___y_4872_ = _args[6];
lean_object* v___y_4873_ = _args[7];
lean_object* v___y_4874_ = _args[8];
lean_object* v___y_4875_ = _args[9];
lean_object* v___y_4876_ = _args[10];
lean_object* v___y_4877_ = _args[11];
lean_object* v___y_4878_ = _args[12];
lean_object* v___y_4879_ = _args[13];
lean_object* v___y_4880_ = _args[14];
lean_object* v___y_4881_ = _args[15];
lean_object* v___y_4882_ = _args[16];
lean_object* v___y_4883_ = _args[17];
_start:
{
size_t v_sz_boxed_4884_; size_t v_i_boxed_4885_; lean_object* v_res_4886_; 
v_sz_boxed_4884_ = lean_unbox_usize(v_sz_4869_);
lean_dec(v_sz_4869_);
v_i_boxed_4885_ = lean_unbox_usize(v_i_4870_);
lean_dec(v_i_4870_);
v_res_4886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(v___x_4866_, v___x_4867_, v_as_4868_, v_sz_boxed_4884_, v_i_boxed_4885_, v_b_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
lean_dec(v___y_4882_);
lean_dec_ref(v___y_4881_);
lean_dec(v___y_4880_);
lean_dec_ref(v___y_4879_);
lean_dec(v___y_4878_);
lean_dec_ref(v___y_4877_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec(v___y_4873_);
lean_dec_ref(v___y_4872_);
lean_dec_ref(v_as_4868_);
lean_dec_ref(v___x_4866_);
return v_res_4886_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(lean_object* v_post_4894_){
_start:
{
lean_object* v___y_4896_; uint8_t v___x_4901_; 
v___x_4901_ = l_Lean_Expr_isLambda(v_post_4894_);
if (v___x_4901_ == 0)
{
v___y_4896_ = v_post_4894_;
goto v___jp_4895_;
}
else
{
lean_object* v___x_4902_; 
v___x_4902_ = l_Lean_Expr_bindingBody_x21(v_post_4894_);
lean_dec_ref(v_post_4894_);
v___y_4896_ = v___x_4902_;
goto v___jp_4895_;
}
v___jp_4895_:
{
lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; uint8_t v___x_4900_; 
v___x_4897_ = l_Lean_Expr_consumeMData(v___y_4896_);
lean_dec_ref(v___y_4896_);
v___x_4898_ = l_Lean_Expr_getAppFn(v___x_4897_);
lean_dec_ref(v___x_4897_);
v___x_4899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2));
v___x_4900_ = l_Lean_Expr_isConstOf(v___x_4898_, v___x_4899_);
lean_dec_ref(v___x_4898_);
return v___x_4900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___boxed(lean_object* v_post_4903_){
_start:
{
uint8_t v_res_4904_; lean_object* v_r_4905_; 
v_res_4904_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(v_post_4903_);
v_r_4905_ = lean_box(v_res_4904_);
return v_r_4905_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(lean_object* v_a_4906_, lean_object* v_x_4907_){
_start:
{
if (lean_obj_tag(v_x_4907_) == 0)
{
uint8_t v___x_4908_; 
v___x_4908_ = 0;
return v___x_4908_;
}
else
{
lean_object* v_head_4909_; lean_object* v_tail_4910_; uint8_t v___x_4911_; 
v_head_4909_ = lean_ctor_get(v_x_4907_, 0);
v_tail_4910_ = lean_ctor_get(v_x_4907_, 1);
v___x_4911_ = lean_name_eq(v_a_4906_, v_head_4909_);
if (v___x_4911_ == 0)
{
v_x_4907_ = v_tail_4910_;
goto _start;
}
else
{
return v___x_4911_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0___boxed(lean_object* v_a_4913_, lean_object* v_x_4914_){
_start:
{
uint8_t v_res_4915_; lean_object* v_r_4916_; 
v_res_4915_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(v_a_4913_, v_x_4914_);
lean_dec(v_x_4914_);
lean_dec(v_a_4913_);
v_r_4916_ = lean_box(v_res_4915_);
return v_r_4916_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(lean_object* v_prog_4965_){
_start:
{
lean_object* v___x_4966_; lean_object* v___x_4967_; 
v___x_4966_ = l_Lean_Expr_getAppFn(v_prog_4965_);
v___x_4967_ = l_Lean_Expr_constName_x3f(v___x_4966_);
lean_dec_ref(v___x_4966_);
if (lean_obj_tag(v___x_4967_) == 0)
{
uint8_t v___x_4968_; 
v___x_4968_ = 0;
return v___x_4968_;
}
else
{
lean_object* v_val_4969_; lean_object* v___x_4970_; uint8_t v___x_4971_; 
v_val_4969_ = lean_ctor_get(v___x_4967_, 0);
lean_inc(v_val_4969_);
lean_dec_ref_known(v___x_4967_, 1);
v___x_4970_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__23));
v___x_4971_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(v_val_4969_, v___x_4970_);
lean_dec(v_val_4969_);
return v___x_4971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___boxed(lean_object* v_prog_4972_){
_start:
{
uint8_t v_res_4973_; lean_object* v_r_4974_; 
v_res_4973_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(v_prog_4972_);
lean_dec_ref(v_prog_4972_);
v_r_4974_ = lean_box(v_res_4973_);
return v_r_4974_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1(void){
_start:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; 
v___x_4976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0));
v___x_4977_ = l_Lean_stringToMessageData(v___x_4976_);
return v___x_4977_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3(void){
_start:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2));
v___x_4980_ = l_Lean_stringToMessageData(v___x_4979_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(lean_object* v_goal_4981_, lean_object* v_info_4982_, lean_object* v_fp_4983_, lean_object* v_F_4984_, lean_object* v_a_4985_, lean_object* v_a_4986_, lean_object* v_a_4987_, lean_object* v_a_4988_, lean_object* v_a_4989_, lean_object* v_a_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_, lean_object* v_a_4995_){
_start:
{
lean_object* v_mkOpAppM_4997_; lean_object* v___x_4998_; 
v_mkOpAppM_4997_ = lean_ctor_get(v_fp_4983_, 1);
lean_inc_ref(v_mkOpAppM_4997_);
lean_dec_ref(v_fp_4983_);
lean_inc(v_a_4995_);
lean_inc_ref(v_a_4994_);
lean_inc(v_a_4993_);
lean_inc_ref(v_a_4992_);
lean_inc_ref(v_info_4982_);
v___x_4998_ = lean_apply_6(v_mkOpAppM_4997_, v_info_4982_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_, lean_box(0));
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_object* v_a_4999_; lean_object* v___x_5000_; 
v_a_4999_ = lean_ctor_get(v___x_4998_, 0);
lean_inc(v_a_4999_);
lean_dec_ref_known(v___x_4998_, 1);
v___x_5000_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_a_4999_, v_info_4982_, v_a_4986_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5000_) == 0)
{
lean_object* v_a_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
lean_inc(v_a_5001_);
lean_dec_ref_known(v___x_5000_, 1);
v___x_5002_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1);
v___x_5003_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_4982_);
lean_dec_ref(v_info_4982_);
v___x_5004_ = l_Lean_indentExpr(v___x_5003_);
lean_inc_ref(v___x_5004_);
v___x_5005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5002_);
lean_ctor_set(v___x_5005_, 1, v___x_5004_);
v___x_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
v___x_5007_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_5001_, v_goal_4981_, v___x_5006_, v_a_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_, v_a_4990_, v_a_4991_, v_a_4992_, v_a_4993_, v_a_4994_, v_a_4995_);
if (lean_obj_tag(v___x_5007_) == 0)
{
lean_object* v_a_5008_; lean_object* v___y_5010_; lean_object* v___y_5011_; lean_object* v___y_5012_; lean_object* v___y_5013_; 
v_a_5008_ = lean_ctor_get(v___x_5007_, 0);
lean_inc(v_a_5008_);
lean_dec_ref_known(v___x_5007_, 1);
if (lean_obj_tag(v_a_5008_) == 1)
{
lean_object* v_mvarIds_5017_; 
v_mvarIds_5017_ = lean_ctor_get(v_a_5008_, 0);
lean_inc(v_mvarIds_5017_);
lean_dec_ref_known(v_a_5008_, 1);
if (lean_obj_tag(v_mvarIds_5017_) == 1)
{
lean_object* v_head_5018_; lean_object* v_tail_5019_; lean_object* v___x_5020_; lean_object* v___x_5022_; uint8_t v_isShared_5023_; uint8_t v_isSharedCheck_5027_; 
lean_dec_ref(v___x_5004_);
v_head_5018_ = lean_ctor_get(v_mvarIds_5017_, 0);
lean_inc(v_head_5018_);
v_tail_5019_ = lean_ctor_get(v_mvarIds_5017_, 1);
lean_inc(v_tail_5019_);
lean_dec_ref_known(v_mvarIds_5017_, 2);
v___x_5020_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_head_5018_, v_F_4984_, v_a_4993_);
v_isSharedCheck_5027_ = !lean_is_exclusive(v___x_5020_);
if (v_isSharedCheck_5027_ == 0)
{
lean_object* v_unused_5028_; 
v_unused_5028_ = lean_ctor_get(v___x_5020_, 0);
lean_dec(v_unused_5028_);
v___x_5022_ = v___x_5020_;
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
else
{
lean_dec(v___x_5020_);
v___x_5022_ = lean_box(0);
v_isShared_5023_ = v_isSharedCheck_5027_;
goto v_resetjp_5021_;
}
v_resetjp_5021_:
{
lean_object* v___x_5025_; 
if (v_isShared_5023_ == 0)
{
lean_ctor_set(v___x_5022_, 0, v_tail_5019_);
v___x_5025_ = v___x_5022_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_tail_5019_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
else
{
lean_dec(v_mvarIds_5017_);
lean_dec_ref(v_F_4984_);
v___y_5010_ = v_a_4992_;
v___y_5011_ = v_a_4993_;
v___y_5012_ = v_a_4994_;
v___y_5013_ = v_a_4995_;
goto v___jp_5009_;
}
}
else
{
lean_dec(v_a_5008_);
lean_dec_ref(v_F_4984_);
v___y_5010_ = v_a_4992_;
v___y_5011_ = v_a_4993_;
v___y_5012_ = v_a_4994_;
v___y_5013_ = v_a_4995_;
goto v___jp_5009_;
}
v___jp_5009_:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; 
v___x_5014_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3);
v___x_5015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5015_, 0, v___x_5014_);
lean_ctor_set(v___x_5015_, 1, v___x_5004_);
v___x_5016_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5015_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
return v___x_5016_;
}
}
else
{
lean_object* v_a_5029_; lean_object* v___x_5031_; uint8_t v_isShared_5032_; uint8_t v_isSharedCheck_5036_; 
lean_dec_ref(v___x_5004_);
lean_dec_ref(v_F_4984_);
v_a_5029_ = lean_ctor_get(v___x_5007_, 0);
v_isSharedCheck_5036_ = !lean_is_exclusive(v___x_5007_);
if (v_isSharedCheck_5036_ == 0)
{
v___x_5031_ = v___x_5007_;
v_isShared_5032_ = v_isSharedCheck_5036_;
goto v_resetjp_5030_;
}
else
{
lean_inc(v_a_5029_);
lean_dec(v___x_5007_);
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
else
{
lean_object* v_a_5037_; lean_object* v___x_5039_; uint8_t v_isShared_5040_; uint8_t v_isSharedCheck_5044_; 
lean_dec_ref(v_F_4984_);
lean_dec_ref(v_info_4982_);
lean_dec(v_goal_4981_);
v_a_5037_ = lean_ctor_get(v___x_5000_, 0);
v_isSharedCheck_5044_ = !lean_is_exclusive(v___x_5000_);
if (v_isSharedCheck_5044_ == 0)
{
v___x_5039_ = v___x_5000_;
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
else
{
lean_inc(v_a_5037_);
lean_dec(v___x_5000_);
v___x_5039_ = lean_box(0);
v_isShared_5040_ = v_isSharedCheck_5044_;
goto v_resetjp_5038_;
}
v_resetjp_5038_:
{
lean_object* v___x_5042_; 
if (v_isShared_5040_ == 0)
{
v___x_5042_ = v___x_5039_;
goto v_reusejp_5041_;
}
else
{
lean_object* v_reuseFailAlloc_5043_; 
v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
v___x_5042_ = v_reuseFailAlloc_5043_;
goto v_reusejp_5041_;
}
v_reusejp_5041_:
{
return v___x_5042_;
}
}
}
}
else
{
lean_object* v_a_5045_; lean_object* v___x_5047_; uint8_t v_isShared_5048_; uint8_t v_isSharedCheck_5052_; 
lean_dec_ref(v_F_4984_);
lean_dec_ref(v_info_4982_);
lean_dec(v_goal_4981_);
v_a_5045_ = lean_ctor_get(v___x_4998_, 0);
v_isSharedCheck_5052_ = !lean_is_exclusive(v___x_4998_);
if (v_isSharedCheck_5052_ == 0)
{
v___x_5047_ = v___x_4998_;
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
else
{
lean_inc(v_a_5045_);
lean_dec(v___x_4998_);
v___x_5047_ = lean_box(0);
v_isShared_5048_ = v_isSharedCheck_5052_;
goto v_resetjp_5046_;
}
v_resetjp_5046_:
{
lean_object* v___x_5050_; 
if (v_isShared_5048_ == 0)
{
v___x_5050_ = v___x_5047_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v_a_5045_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
return v___x_5050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___boxed(lean_object* v_goal_5053_, lean_object* v_info_5054_, lean_object* v_fp_5055_, lean_object* v_F_5056_, lean_object* v_a_5057_, lean_object* v_a_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_, lean_object* v_a_5065_, lean_object* v_a_5066_, lean_object* v_a_5067_, lean_object* v_a_5068_){
_start:
{
lean_object* v_res_5069_; 
v_res_5069_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5053_, v_info_5054_, v_fp_5055_, v_F_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_, v_a_5063_, v_a_5064_, v_a_5065_, v_a_5066_, v_a_5067_);
lean_dec(v_a_5067_);
lean_dec_ref(v_a_5066_);
lean_dec(v_a_5065_);
lean_dec_ref(v_a_5064_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
lean_dec(v_a_5059_);
lean_dec(v_a_5058_);
lean_dec_ref(v_a_5057_);
return v_res_5069_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(lean_object* v_as_x27_5073_, lean_object* v_b_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
if (lean_obj_tag(v_as_x27_5073_) == 0)
{
lean_object* v___x_5082_; 
v___x_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5082_, 0, v_b_5074_);
return v___x_5082_;
}
else
{
lean_object* v_head_5083_; lean_object* v_tail_5084_; lean_object* v___x_5085_; 
lean_dec_ref(v_b_5074_);
v_head_5083_ = lean_ctor_get(v_as_x27_5073_, 0);
v_tail_5084_ = lean_ctor_get(v_as_x27_5073_, 1);
lean_inc(v_head_5083_);
v___x_5085_ = l_Lean_MVarId_getType(v_head_5083_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; uint8_t v___x_5090_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref_known(v___x_5085_, 1);
v___x_5087_ = lean_box(0);
v___x_5088_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5089_ = lean_unsigned_to_nat(4u);
v___x_5090_ = l_Lean_Expr_isAppOfArity(v_a_5086_, v___x_5088_, v___x_5089_);
if (v___x_5090_ == 0)
{
lean_object* v___x_5091_; 
lean_dec(v_a_5086_);
v___x_5091_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0));
v_as_x27_5073_ = v_tail_5084_;
v_b_5074_ = v___x_5091_;
goto _start;
}
else
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = l_Lean_Expr_appArg_x21(v_a_5086_);
lean_dec(v_a_5086_);
v___x_5094_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v___x_5093_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5097_; uint8_t v_isShared_5098_; uint8_t v_isSharedCheck_5105_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5105_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5105_ == 0)
{
v___x_5097_ = v___x_5094_;
v_isShared_5098_ = v_isSharedCheck_5105_;
goto v_resetjp_5096_;
}
else
{
lean_inc(v_a_5095_);
lean_dec(v___x_5094_);
v___x_5097_ = lean_box(0);
v_isShared_5098_ = v_isSharedCheck_5105_;
goto v_resetjp_5096_;
}
v_resetjp_5096_:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5103_; 
v___x_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5099_, 0, v_a_5095_);
v___x_5100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5100_, 0, v___x_5099_);
v___x_5101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5101_, 0, v___x_5100_);
lean_ctor_set(v___x_5101_, 1, v___x_5087_);
if (v_isShared_5098_ == 0)
{
lean_ctor_set(v___x_5097_, 0, v___x_5101_);
v___x_5103_ = v___x_5097_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5101_);
v___x_5103_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
return v___x_5103_;
}
}
}
else
{
lean_object* v_a_5106_; lean_object* v___x_5108_; uint8_t v_isShared_5109_; uint8_t v_isSharedCheck_5113_; 
v_a_5106_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5113_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5113_ == 0)
{
v___x_5108_ = v___x_5094_;
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
else
{
lean_inc(v_a_5106_);
lean_dec(v___x_5094_);
v___x_5108_ = lean_box(0);
v_isShared_5109_ = v_isSharedCheck_5113_;
goto v_resetjp_5107_;
}
v_resetjp_5107_:
{
lean_object* v___x_5111_; 
if (v_isShared_5109_ == 0)
{
v___x_5111_ = v___x_5108_;
goto v_reusejp_5110_;
}
else
{
lean_object* v_reuseFailAlloc_5112_; 
v_reuseFailAlloc_5112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_a_5106_);
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
}
else
{
lean_object* v_a_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5121_; 
v_a_5114_ = lean_ctor_get(v___x_5085_, 0);
v_isSharedCheck_5121_ = !lean_is_exclusive(v___x_5085_);
if (v_isSharedCheck_5121_ == 0)
{
v___x_5116_ = v___x_5085_;
v_isShared_5117_ = v_isSharedCheck_5121_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_a_5114_);
lean_dec(v___x_5085_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_5122_, lean_object* v_b_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_res_5131_; 
v_res_5131_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(v_as_x27_5122_, v_b_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
lean_dec(v___y_5129_);
lean_dec_ref(v___y_5128_);
lean_dec(v___y_5127_);
lean_dec_ref(v___y_5126_);
lean_dec(v___y_5125_);
lean_dec_ref(v___y_5124_);
lean_dec(v_as_x27_5122_);
return v_res_5131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(lean_object* v_subgoals_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_, lean_object* v_a_5136_, lean_object* v_a_5137_, lean_object* v_a_5138_, lean_object* v_a_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_, lean_object* v_a_5142_, lean_object* v_a_5143_){
_start:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; 
v___x_5145_ = lean_box(0);
v___x_5146_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0));
v___x_5147_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(v_subgoals_5132_, v___x_5146_, v_a_5138_, v_a_5139_, v_a_5140_, v_a_5141_, v_a_5142_, v_a_5143_);
if (lean_obj_tag(v___x_5147_) == 0)
{
lean_object* v_a_5148_; lean_object* v___x_5150_; uint8_t v_isShared_5151_; uint8_t v_isSharedCheck_5160_; 
v_a_5148_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5150_ = v___x_5147_;
v_isShared_5151_ = v_isSharedCheck_5160_;
goto v_resetjp_5149_;
}
else
{
lean_inc(v_a_5148_);
lean_dec(v___x_5147_);
v___x_5150_ = lean_box(0);
v_isShared_5151_ = v_isSharedCheck_5160_;
goto v_resetjp_5149_;
}
v_resetjp_5149_:
{
lean_object* v_fst_5152_; 
v_fst_5152_ = lean_ctor_get(v_a_5148_, 0);
lean_inc(v_fst_5152_);
lean_dec(v_a_5148_);
if (lean_obj_tag(v_fst_5152_) == 0)
{
lean_object* v___x_5154_; 
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 0, v___x_5145_);
v___x_5154_ = v___x_5150_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5145_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
else
{
lean_object* v_val_5156_; lean_object* v___x_5158_; 
v_val_5156_ = lean_ctor_get(v_fst_5152_, 0);
lean_inc(v_val_5156_);
lean_dec_ref_known(v_fst_5152_, 1);
if (v_isShared_5151_ == 0)
{
lean_ctor_set(v___x_5150_, 0, v_val_5156_);
v___x_5158_ = v___x_5150_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_val_5156_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
return v___x_5158_;
}
}
}
}
else
{
lean_object* v_a_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5168_; 
v_a_5161_ = lean_ctor_get(v___x_5147_, 0);
v_isSharedCheck_5168_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5168_ == 0)
{
v___x_5163_ = v___x_5147_;
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_a_5161_);
lean_dec(v___x_5147_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5168_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5166_; 
if (v_isShared_5164_ == 0)
{
v___x_5166_ = v___x_5163_;
goto v_reusejp_5165_;
}
else
{
lean_object* v_reuseFailAlloc_5167_; 
v_reuseFailAlloc_5167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5167_, 0, v_a_5161_);
v___x_5166_ = v_reuseFailAlloc_5167_;
goto v_reusejp_5165_;
}
v_reusejp_5165_:
{
return v___x_5166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f___boxed(lean_object* v_subgoals_5169_, lean_object* v_a_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_, lean_object* v_a_5173_, lean_object* v_a_5174_, lean_object* v_a_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_, lean_object* v_a_5180_, lean_object* v_a_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(v_subgoals_5169_, v_a_5170_, v_a_5171_, v_a_5172_, v_a_5173_, v_a_5174_, v_a_5175_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_, v_a_5180_);
lean_dec(v_a_5180_);
lean_dec_ref(v_a_5179_);
lean_dec(v_a_5178_);
lean_dec_ref(v_a_5177_);
lean_dec(v_a_5176_);
lean_dec_ref(v_a_5175_);
lean_dec(v_a_5174_);
lean_dec_ref(v_a_5173_);
lean_dec(v_a_5172_);
lean_dec(v_a_5171_);
lean_dec_ref(v_a_5170_);
lean_dec(v_subgoals_5169_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0(lean_object* v_as_5183_, lean_object* v_as_x27_5184_, lean_object* v_b_5185_, lean_object* v_a_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_, lean_object* v___y_5192_, lean_object* v___y_5193_, lean_object* v___y_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_, lean_object* v___y_5197_){
_start:
{
lean_object* v___x_5199_; 
v___x_5199_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(v_as_x27_5184_, v_b_5185_, v___y_5192_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_);
return v___x_5199_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___boxed(lean_object* v_as_5200_, lean_object* v_as_x27_5201_, lean_object* v_b_5202_, lean_object* v_a_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_){
_start:
{
lean_object* v_res_5216_; 
v_res_5216_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0(v_as_5200_, v_as_x27_5201_, v_b_5202_, v_a_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
lean_dec(v___y_5214_);
lean_dec_ref(v___y_5213_);
lean_dec(v___y_5212_);
lean_dec_ref(v___y_5211_);
lean_dec(v___y_5210_);
lean_dec_ref(v___y_5209_);
lean_dec(v___y_5208_);
lean_dec_ref(v___y_5207_);
lean_dec(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v_as_x27_5201_);
lean_dec(v_as_5200_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(lean_object* v_a_5217_, lean_object* v_x_5218_){
_start:
{
if (lean_obj_tag(v_x_5218_) == 0)
{
lean_object* v___x_5219_; 
v___x_5219_ = lean_box(0);
return v___x_5219_;
}
else
{
lean_object* v_key_5220_; lean_object* v_value_5221_; lean_object* v_tail_5222_; uint8_t v___x_5223_; 
v_key_5220_ = lean_ctor_get(v_x_5218_, 0);
v_value_5221_ = lean_ctor_get(v_x_5218_, 1);
v_tail_5222_ = lean_ctor_get(v_x_5218_, 2);
v___x_5223_ = lean_name_eq(v_key_5220_, v_a_5217_);
if (v___x_5223_ == 0)
{
v_x_5218_ = v_tail_5222_;
goto _start;
}
else
{
lean_object* v___x_5225_; 
lean_inc(v_value_5221_);
v___x_5225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5225_, 0, v_value_5221_);
return v___x_5225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg___boxed(lean_object* v_a_5226_, lean_object* v_x_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(v_a_5226_, v_x_5227_);
lean_dec(v_x_5227_);
lean_dec(v_a_5226_);
return v_res_5228_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5229_; uint64_t v___x_5230_; 
v___x_5229_ = lean_unsigned_to_nat(1723u);
v___x_5230_ = lean_uint64_of_nat(v___x_5229_);
return v___x_5230_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(lean_object* v_m_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v_buckets_5233_; lean_object* v___x_5234_; uint64_t v___y_5236_; 
v_buckets_5233_ = lean_ctor_get(v_m_5231_, 1);
v___x_5234_ = lean_array_get_size(v_buckets_5233_);
if (lean_obj_tag(v_a_5232_) == 0)
{
uint64_t v___x_5250_; 
v___x_5250_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0);
v___y_5236_ = v___x_5250_;
goto v___jp_5235_;
}
else
{
uint64_t v_hash_5251_; 
v_hash_5251_ = lean_ctor_get_uint64(v_a_5232_, sizeof(void*)*2);
v___y_5236_ = v_hash_5251_;
goto v___jp_5235_;
}
v___jp_5235_:
{
uint64_t v___x_5237_; uint64_t v___x_5238_; uint64_t v_fold_5239_; uint64_t v___x_5240_; uint64_t v___x_5241_; uint64_t v___x_5242_; size_t v___x_5243_; size_t v___x_5244_; size_t v___x_5245_; size_t v___x_5246_; size_t v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; 
v___x_5237_ = 32ULL;
v___x_5238_ = lean_uint64_shift_right(v___y_5236_, v___x_5237_);
v_fold_5239_ = lean_uint64_xor(v___y_5236_, v___x_5238_);
v___x_5240_ = 16ULL;
v___x_5241_ = lean_uint64_shift_right(v_fold_5239_, v___x_5240_);
v___x_5242_ = lean_uint64_xor(v_fold_5239_, v___x_5241_);
v___x_5243_ = lean_uint64_to_usize(v___x_5242_);
v___x_5244_ = lean_usize_of_nat(v___x_5234_);
v___x_5245_ = ((size_t)1ULL);
v___x_5246_ = lean_usize_sub(v___x_5244_, v___x_5245_);
v___x_5247_ = lean_usize_land(v___x_5243_, v___x_5246_);
v___x_5248_ = lean_array_uget_borrowed(v_buckets_5233_, v___x_5247_);
v___x_5249_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(v_a_5232_, v___x_5248_);
return v___x_5249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___boxed(lean_object* v_m_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(v_m_5252_, v_a_5253_);
lean_dec(v_a_5253_);
lean_dec_ref(v_m_5252_);
return v_res_5254_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5256_; lean_object* v___x_5257_; 
v___x_5256_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__0));
v___x_5257_ = l_Lean_stringToMessageData(v___x_5256_);
return v___x_5257_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5259_; lean_object* v___x_5260_; 
v___x_5259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__2));
v___x_5260_ = l_Lean_stringToMessageData(v___x_5259_);
return v___x_5260_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__4));
v___x_5263_ = l_Lean_stringToMessageData(v___x_5262_);
return v___x_5263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0(lean_object* v_scope_5264_, lean_object* v___x_5265_, lean_object* v___x_5266_, lean_object* v_goal_5267_, lean_object* v_info_5268_, lean_object* v_pre_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_, lean_object* v___y_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_){
_start:
{
lean_object* v___x_5282_; 
lean_inc_ref(v___x_5266_);
lean_inc_ref(v___x_5265_);
v___x_5282_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(v_scope_5264_, v___x_5265_, v___x_5266_, v___y_5270_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5285_; uint8_t v_isShared_5286_; uint8_t v_isSharedCheck_5493_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5493_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5493_ == 0)
{
v___x_5285_ = v___x_5282_;
v_isShared_5286_ = v_isSharedCheck_5493_;
goto v_resetjp_5284_;
}
else
{
lean_inc(v_a_5283_);
lean_dec(v___x_5282_);
v___x_5285_ = lean_box(0);
v_isShared_5286_ = v_isSharedCheck_5493_;
goto v_resetjp_5284_;
}
v_resetjp_5284_:
{
lean_object* v_fst_5287_; lean_object* v_snd_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5492_; 
v_fst_5287_ = lean_ctor_get(v_a_5283_, 0);
v_snd_5288_ = lean_ctor_get(v_a_5283_, 1);
v_isSharedCheck_5492_ = !lean_is_exclusive(v_a_5283_);
if (v_isSharedCheck_5492_ == 0)
{
v___x_5290_ = v_a_5283_;
v_isShared_5291_ = v_isSharedCheck_5492_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_snd_5288_);
lean_inc(v_fst_5287_);
lean_dec(v_a_5283_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5492_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___y_5293_; lean_object* v___y_5301_; lean_object* v___y_5302_; lean_object* v___y_5303_; lean_object* v___y_5304_; lean_object* v___y_5305_; lean_object* v___y_5306_; lean_object* v___y_5307_; lean_object* v___y_5308_; lean_object* v___y_5309_; lean_object* v___y_5310_; lean_object* v___y_5311_; lean_object* v___y_5312_; lean_object* v___y_5313_; lean_object* v___y_5314_; 
if (lean_obj_tag(v_snd_5288_) == 0)
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5266_);
lean_dec_ref(v___x_5265_);
v_a_5342_ = lean_ctor_get(v_snd_5288_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v_snd_5288_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v_snd_5288_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v_snd_5288_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
else
{
lean_object* v_a_5350_; lean_object* v___y_5352_; uint8_t v___y_5480_; uint8_t v___x_5489_; 
v_a_5350_ = lean_ctor_get(v_snd_5288_, 0);
lean_inc(v_a_5350_);
lean_dec_ref_known(v_snd_5288_, 1);
v___x_5489_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(v___x_5265_);
if (v___x_5489_ == 0)
{
lean_object* v___x_5490_; uint8_t v___x_5491_; 
v___x_5490_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(v_info_5268_);
v___x_5491_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(v___x_5490_);
v___y_5480_ = v___x_5491_;
goto v___jp_5479_;
}
else
{
v___y_5480_ = v___x_5489_;
goto v___jp_5479_;
}
v___jp_5351_:
{
lean_object* v_resourceTy_5353_; lean_object* v_proc_5354_; lean_object* v___x_5355_; 
v_resourceTy_5353_ = lean_ctor_get(v___y_5352_, 2);
v_proc_5354_ = lean_ctor_get(v___y_5352_, 4);
lean_inc_ref(v_resourceTy_5353_);
lean_inc(v___y_5280_);
lean_inc_ref(v___y_5279_);
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
lean_inc_ref(v_info_5268_);
v___x_5355_ = lean_apply_6(v_resourceTy_5353_, v_info_5268_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, lean_box(0));
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5357_; 
v_a_5356_ = lean_ctor_get(v___x_5355_, 0);
lean_inc_n(v_a_5356_, 2);
lean_dec_ref_known(v___x_5355_, 1);
v___x_5357_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_a_5356_, v_info_5268_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v_a_5358_; 
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
lean_inc(v_a_5358_);
lean_dec_ref_known(v___x_5357_, 1);
if (lean_obj_tag(v_a_5358_) == 1)
{
lean_object* v_val_5359_; lean_object* v___x_5360_; 
lean_dec(v_a_5356_);
lean_dec(v_a_5350_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v___x_5265_);
v_val_5359_ = lean_ctor_get(v_a_5358_, 0);
lean_inc(v_val_5359_);
lean_dec_ref_known(v_a_5358_, 1);
v___x_5360_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5267_, v_info_5268_, v___y_5352_, v_val_5359_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; lean_object* v___x_5363_; uint8_t v_isShared_5364_; uint8_t v_isSharedCheck_5369_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5363_ = v___x_5360_;
v_isShared_5364_ = v_isSharedCheck_5369_;
goto v_resetjp_5362_;
}
else
{
lean_inc(v_a_5361_);
lean_dec(v___x_5360_);
v___x_5363_ = lean_box(0);
v_isShared_5364_ = v_isSharedCheck_5369_;
goto v_resetjp_5362_;
}
v_resetjp_5362_:
{
lean_object* v___x_5365_; lean_object* v___x_5367_; 
v___x_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5365_, 0, v_fst_5287_);
lean_ctor_set(v___x_5365_, 1, v_a_5361_);
if (v_isShared_5364_ == 0)
{
lean_ctor_set(v___x_5363_, 0, v___x_5365_);
v___x_5367_ = v___x_5363_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v___x_5365_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
else
{
lean_object* v_a_5370_; lean_object* v___x_5372_; uint8_t v_isShared_5373_; uint8_t v_isSharedCheck_5377_; 
lean_dec(v_fst_5287_);
v_a_5370_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5377_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5377_ == 0)
{
v___x_5372_ = v___x_5360_;
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
else
{
lean_inc(v_a_5370_);
lean_dec(v___x_5360_);
v___x_5372_ = lean_box(0);
v_isShared_5373_ = v_isSharedCheck_5377_;
goto v_resetjp_5371_;
}
v_resetjp_5371_:
{
lean_object* v___x_5375_; 
if (v_isShared_5373_ == 0)
{
v___x_5375_ = v___x_5372_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5376_; 
v_reuseFailAlloc_5376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_a_5370_);
v___x_5375_ = v_reuseFailAlloc_5376_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
return v___x_5375_;
}
}
}
}
else
{
lean_dec(v_a_5358_);
if (lean_obj_tag(v_proc_5354_) == 1)
{
lean_object* v_val_5378_; lean_object* v___x_5379_; 
v_val_5378_ = lean_ctor_get(v_proc_5354_, 0);
v___x_5379_ = l_Lean_Meta_saveState___redArg(v___y_5278_, v___y_5280_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v___x_5381_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
lean_inc(v_a_5380_);
lean_dec_ref_known(v___x_5379_, 1);
lean_inc_ref(v_info_5268_);
lean_inc(v_goal_5267_);
lean_inc(v_fst_5287_);
v___x_5381_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_fst_5287_, v_goal_5267_, v_info_5268_, v_a_5350_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5381_) == 0)
{
lean_object* v_a_5382_; 
v_a_5382_ = lean_ctor_get(v___x_5381_, 0);
lean_inc(v_a_5382_);
lean_dec_ref_known(v___x_5381_, 1);
if (lean_obj_tag(v_a_5382_) == 0)
{
lean_object* v_subgoals_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5444_; 
v_subgoals_5383_ = lean_ctor_get(v_a_5382_, 1);
v_isSharedCheck_5444_ = !lean_is_exclusive(v_a_5382_);
if (v_isSharedCheck_5444_ == 0)
{
lean_object* v_unused_5445_; 
v_unused_5445_ = lean_ctor_get(v_a_5382_, 0);
lean_dec(v_unused_5445_);
v___x_5385_ = v_a_5382_;
v_isShared_5386_ = v_isSharedCheck_5444_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_subgoals_5383_);
lean_dec(v_a_5382_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5444_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5387_; 
v___x_5387_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(v_subgoals_5383_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5387_) == 0)
{
lean_object* v_a_5388_; 
v_a_5388_ = lean_ctor_get(v___x_5387_, 0);
lean_inc(v_a_5388_);
lean_dec_ref_known(v___x_5387_, 1);
if (lean_obj_tag(v_a_5388_) == 0)
{
lean_del_object(v___x_5385_);
lean_dec(v_a_5380_);
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v___y_5293_ = v_subgoals_5383_;
goto v___jp_5292_;
}
else
{
lean_object* v_val_5389_; lean_object* v___x_5390_; 
v_val_5389_ = lean_ctor_get(v_a_5388_, 0);
lean_inc(v_val_5389_);
lean_dec_ref_known(v_a_5388_, 1);
lean_inc(v_val_5378_);
lean_inc(v___y_5280_);
lean_inc_ref(v___y_5279_);
lean_inc(v___y_5278_);
lean_inc_ref(v___y_5277_);
lean_inc(v___y_5276_);
lean_inc_ref(v___y_5275_);
lean_inc_ref(v_info_5268_);
v___x_5390_ = lean_apply_11(v_val_5378_, v_a_5356_, v_pre_5269_, v_info_5268_, v_val_5389_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, lean_box(0));
if (lean_obj_tag(v___x_5390_) == 0)
{
lean_object* v_a_5391_; 
v_a_5391_ = lean_ctor_get(v___x_5390_, 0);
lean_inc(v_a_5391_);
lean_dec_ref_known(v___x_5390_, 1);
if (lean_obj_tag(v_a_5391_) == 1)
{
lean_object* v_val_5392_; lean_object* v___x_5393_; 
lean_dec(v_subgoals_5383_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5285_);
v_val_5392_ = lean_ctor_get(v_a_5391_, 0);
lean_inc(v_val_5392_);
lean_dec_ref_known(v_a_5391_, 1);
v___x_5393_ = l_Lean_Meta_Sym_instantiateMVarsS(v_val_5392_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5393_) == 0)
{
lean_object* v_options_5394_; uint8_t v_hasTrace_5395_; 
v_options_5394_ = lean_ctor_get(v___y_5279_, 2);
v_hasTrace_5395_ = lean_ctor_get_uint8(v_options_5394_, sizeof(void*)*1);
if (v_hasTrace_5395_ == 0)
{
lean_object* v_a_5396_; 
lean_del_object(v___x_5385_);
lean_dec_ref(v___x_5265_);
v_a_5396_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5396_);
lean_dec_ref_known(v___x_5393_, 1);
v___y_5301_ = v___y_5352_;
v___y_5302_ = v_a_5380_;
v___y_5303_ = v_a_5396_;
v___y_5304_ = v___y_5270_;
v___y_5305_ = v___y_5271_;
v___y_5306_ = v___y_5272_;
v___y_5307_ = v___y_5273_;
v___y_5308_ = v___y_5274_;
v___y_5309_ = v___y_5275_;
v___y_5310_ = v___y_5276_;
v___y_5311_ = v___y_5277_;
v___y_5312_ = v___y_5278_;
v___y_5313_ = v___y_5279_;
v___y_5314_ = v___y_5280_;
goto v___jp_5300_;
}
else
{
lean_object* v_a_5397_; lean_object* v_inheritedTraceOptions_5398_; lean_object* v___x_5399_; lean_object* v___x_5400_; uint8_t v___x_5401_; 
v_a_5397_ = lean_ctor_get(v___x_5393_, 0);
lean_inc(v_a_5397_);
lean_dec_ref_known(v___x_5393_, 1);
v_inheritedTraceOptions_5398_ = lean_ctor_get(v___y_5279_, 13);
v___x_5399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_5400_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5398_, v_options_5394_, v___x_5400_);
if (v___x_5401_ == 0)
{
lean_del_object(v___x_5385_);
lean_dec_ref(v___x_5265_);
v___y_5301_ = v___y_5352_;
v___y_5302_ = v_a_5380_;
v___y_5303_ = v_a_5397_;
v___y_5304_ = v___y_5270_;
v___y_5305_ = v___y_5271_;
v___y_5306_ = v___y_5272_;
v___y_5307_ = v___y_5273_;
v___y_5308_ = v___y_5274_;
v___y_5309_ = v___y_5275_;
v___y_5310_ = v___y_5276_;
v___y_5311_ = v___y_5277_;
v___y_5312_ = v___y_5278_;
v___y_5313_ = v___y_5279_;
v___y_5314_ = v___y_5280_;
goto v___jp_5300_;
}
else
{
lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5405_; 
v___x_5402_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1);
v___x_5403_ = l_Lean_MessageData_ofExpr(v___x_5265_);
if (v_isShared_5386_ == 0)
{
lean_ctor_set_tag(v___x_5385_, 7);
lean_ctor_set(v___x_5385_, 1, v___x_5403_);
lean_ctor_set(v___x_5385_, 0, v___x_5402_);
v___x_5405_ = v___x_5385_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v___x_5402_);
lean_ctor_set(v_reuseFailAlloc_5419_, 1, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
v___x_5406_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3);
v___x_5407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5407_, 0, v___x_5405_);
lean_ctor_set(v___x_5407_, 1, v___x_5406_);
lean_inc(v_a_5397_);
v___x_5408_ = l_Lean_indentExpr(v_a_5397_);
v___x_5409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5407_);
lean_ctor_set(v___x_5409_, 1, v___x_5408_);
v___x_5410_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5399_, v___x_5409_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
if (lean_obj_tag(v___x_5410_) == 0)
{
lean_dec_ref_known(v___x_5410_, 1);
v___y_5301_ = v___y_5352_;
v___y_5302_ = v_a_5380_;
v___y_5303_ = v_a_5397_;
v___y_5304_ = v___y_5270_;
v___y_5305_ = v___y_5271_;
v___y_5306_ = v___y_5272_;
v___y_5307_ = v___y_5273_;
v___y_5308_ = v___y_5274_;
v___y_5309_ = v___y_5275_;
v___y_5310_ = v___y_5276_;
v___y_5311_ = v___y_5277_;
v___y_5312_ = v___y_5278_;
v___y_5313_ = v___y_5279_;
v___y_5314_ = v___y_5280_;
goto v___jp_5300_;
}
else
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5418_; 
lean_dec(v_a_5397_);
lean_dec(v_a_5380_);
lean_dec_ref(v___y_5352_);
lean_dec(v_fst_5287_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
v_a_5411_ = lean_ctor_get(v___x_5410_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5410_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5413_ = v___x_5410_;
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5410_);
v___x_5413_ = lean_box(0);
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
v_resetjp_5412_:
{
lean_object* v___x_5416_; 
if (v_isShared_5414_ == 0)
{
v___x_5416_ = v___x_5413_;
goto v_reusejp_5415_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v_a_5411_);
v___x_5416_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5415_;
}
v_reusejp_5415_:
{
return v___x_5416_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5420_; lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5427_; 
lean_del_object(v___x_5385_);
lean_dec(v_a_5380_);
lean_dec_ref(v___y_5352_);
lean_dec(v_fst_5287_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v_a_5420_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5427_ == 0)
{
v___x_5422_ = v___x_5393_;
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
else
{
lean_inc(v_a_5420_);
lean_dec(v___x_5393_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5427_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5425_; 
if (v_isShared_5423_ == 0)
{
v___x_5425_ = v___x_5422_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v_a_5420_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
}
else
{
lean_dec(v_a_5391_);
lean_del_object(v___x_5385_);
lean_dec(v_a_5380_);
lean_dec_ref(v___y_5352_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v___y_5293_ = v_subgoals_5383_;
goto v___jp_5292_;
}
}
else
{
lean_object* v_a_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5435_; 
lean_del_object(v___x_5385_);
lean_dec(v_subgoals_5383_);
lean_dec(v_a_5380_);
lean_dec_ref(v___y_5352_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v_a_5428_ = lean_ctor_get(v___x_5390_, 0);
v_isSharedCheck_5435_ = !lean_is_exclusive(v___x_5390_);
if (v_isSharedCheck_5435_ == 0)
{
v___x_5430_ = v___x_5390_;
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_a_5428_);
lean_dec(v___x_5390_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5435_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5433_; 
if (v_isShared_5431_ == 0)
{
v___x_5433_ = v___x_5430_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v_a_5428_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
}
else
{
lean_object* v_a_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5443_; 
lean_del_object(v___x_5385_);
lean_dec(v_subgoals_5383_);
lean_dec(v_a_5380_);
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v_a_5436_ = lean_ctor_get(v___x_5387_, 0);
v_isSharedCheck_5443_ = !lean_is_exclusive(v___x_5387_);
if (v_isSharedCheck_5443_ == 0)
{
v___x_5438_ = v___x_5387_;
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_a_5436_);
lean_dec(v___x_5387_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5443_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v___x_5441_; 
if (v_isShared_5439_ == 0)
{
v___x_5441_ = v___x_5438_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5442_; 
v_reuseFailAlloc_5442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5436_);
v___x_5441_ = v_reuseFailAlloc_5442_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
return v___x_5441_;
}
}
}
}
}
else
{
lean_object* v___x_5446_; lean_object* v___x_5447_; lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; 
lean_dec(v_a_5382_);
lean_dec(v_a_5380_);
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
v___x_5446_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3);
v___x_5447_ = l_Lean_indentExpr(v___x_5265_);
v___x_5448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5448_, 0, v___x_5446_);
lean_ctor_set(v___x_5448_, 1, v___x_5447_);
v___x_5449_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5);
v___x_5450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5450_, 0, v___x_5448_);
lean_ctor_set(v___x_5450_, 1, v___x_5449_);
v___x_5451_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5450_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
return v___x_5451_;
}
}
else
{
lean_dec(v_a_5380_);
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
return v___x_5381_;
}
}
else
{
lean_object* v_a_5452_; lean_object* v___x_5454_; uint8_t v_isShared_5455_; uint8_t v_isSharedCheck_5459_; 
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_dec(v_a_5350_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v_a_5452_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5459_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5459_ == 0)
{
v___x_5454_ = v___x_5379_;
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
else
{
lean_inc(v_a_5452_);
lean_dec(v___x_5379_);
v___x_5454_ = lean_box(0);
v_isShared_5455_ = v_isSharedCheck_5459_;
goto v_resetjp_5453_;
}
v_resetjp_5453_:
{
lean_object* v___x_5457_; 
if (v_isShared_5455_ == 0)
{
v___x_5457_ = v___x_5454_;
goto v_reusejp_5456_;
}
else
{
lean_object* v_reuseFailAlloc_5458_; 
v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5458_, 0, v_a_5452_);
v___x_5457_ = v_reuseFailAlloc_5458_;
goto v_reusejp_5456_;
}
v_reusejp_5456_:
{
return v___x_5457_;
}
}
}
}
else
{
lean_object* v___x_5460_; 
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_del_object(v___x_5290_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v___x_5265_);
v___x_5460_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_fst_5287_, v_goal_5267_, v_info_5268_, v_a_5350_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
return v___x_5460_;
}
}
}
else
{
lean_object* v_a_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5468_; 
lean_dec(v_a_5356_);
lean_dec_ref(v___y_5352_);
lean_dec(v_a_5350_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v_a_5461_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5463_ = v___x_5357_;
v_isShared_5464_ = v_isSharedCheck_5468_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_a_5461_);
lean_dec(v___x_5357_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5468_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5466_; 
if (v_isShared_5464_ == 0)
{
v___x_5466_ = v___x_5463_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5461_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
}
else
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5476_; 
lean_dec_ref(v___y_5352_);
lean_dec(v_a_5350_);
lean_del_object(v___x_5290_);
lean_dec(v_fst_5287_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5265_);
v_a_5469_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5471_ = v___x_5355_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5355_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5474_; 
if (v_isShared_5472_ == 0)
{
v___x_5474_ = v___x_5471_;
goto v_reusejp_5473_;
}
else
{
lean_object* v_reuseFailAlloc_5475_; 
v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
v___x_5474_ = v_reuseFailAlloc_5475_;
goto v_reusejp_5473_;
}
v_reusejp_5473_:
{
return v___x_5474_;
}
}
}
}
v___jp_5477_:
{
lean_object* v___x_5478_; 
v___x_5478_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc;
v___y_5352_ = v___x_5478_;
goto v___jp_5351_;
}
v___jp_5479_:
{
if (v___y_5480_ == 0)
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = l_Lean_Expr_getAppFn(v___x_5266_);
lean_dec_ref(v___x_5266_);
v___x_5482_ = l_Lean_Expr_constName_x3f(v___x_5481_);
lean_dec_ref(v___x_5481_);
if (lean_obj_tag(v___x_5482_) == 0)
{
goto v___jp_5477_;
}
else
{
lean_object* v_frameProcs_5483_; lean_object* v_val_5484_; lean_object* v_byProg_5485_; lean_object* v___x_5486_; 
v_frameProcs_5483_ = lean_ctor_get(v___y_5270_, 1);
v_val_5484_ = lean_ctor_get(v___x_5482_, 0);
lean_inc(v_val_5484_);
lean_dec_ref_known(v___x_5482_, 1);
v_byProg_5485_ = lean_ctor_get(v_frameProcs_5483_, 0);
v___x_5486_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(v_byProg_5485_, v_val_5484_);
lean_dec(v_val_5484_);
if (lean_obj_tag(v___x_5486_) == 0)
{
goto v___jp_5477_;
}
else
{
lean_object* v_val_5487_; 
v_val_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_val_5487_);
lean_dec_ref_known(v___x_5486_, 1);
v___y_5352_ = v_val_5487_;
goto v___jp_5351_;
}
}
}
else
{
lean_object* v___x_5488_; 
lean_del_object(v___x_5290_);
lean_del_object(v___x_5285_);
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v___x_5266_);
lean_dec_ref(v___x_5265_);
v___x_5488_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_fst_5287_, v_goal_5267_, v_info_5268_, v_a_5350_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_);
return v___x_5488_;
}
}
}
v___jp_5292_:
{
lean_object* v___x_5295_; 
if (v_isShared_5291_ == 0)
{
lean_ctor_set(v___x_5290_, 1, v___y_5293_);
v___x_5295_ = v___x_5290_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_fst_5287_);
lean_ctor_set(v_reuseFailAlloc_5299_, 1, v___y_5293_);
v___x_5295_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
lean_object* v___x_5297_; 
if (v_isShared_5286_ == 0)
{
lean_ctor_set(v___x_5285_, 0, v___x_5295_);
v___x_5297_ = v___x_5285_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5298_; 
v_reuseFailAlloc_5298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5298_, 0, v___x_5295_);
v___x_5297_ = v_reuseFailAlloc_5298_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
return v___x_5297_;
}
}
}
v___jp_5300_:
{
lean_object* v___x_5315_; 
v___x_5315_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5302_, v___y_5312_, v___y_5314_);
lean_dec_ref(v___y_5302_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v___x_5316_; 
lean_dec_ref_known(v___x_5315_, 1);
v___x_5316_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5267_, v_info_5268_, v___y_5301_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_, v___y_5314_);
if (lean_obj_tag(v___x_5316_) == 0)
{
lean_object* v_a_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5325_; 
v_a_5317_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5319_ = v___x_5316_;
v_isShared_5320_ = v_isSharedCheck_5325_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_a_5317_);
lean_dec(v___x_5316_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5325_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___x_5321_; lean_object* v___x_5323_; 
v___x_5321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5321_, 0, v_fst_5287_);
lean_ctor_set(v___x_5321_, 1, v_a_5317_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 0, v___x_5321_);
v___x_5323_ = v___x_5319_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5321_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
else
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
lean_dec(v_fst_5287_);
v_a_5326_ = lean_ctor_get(v___x_5316_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5316_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5328_ = v___x_5316_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5316_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
}
else
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
lean_dec_ref(v___y_5303_);
lean_dec_ref(v___y_5301_);
lean_dec(v_fst_5287_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
v_a_5334_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5336_ = v___x_5315_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5315_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5339_; 
if (v_isShared_5337_ == 0)
{
v___x_5339_ = v___x_5336_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
return v___x_5339_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5494_; lean_object* v___x_5496_; uint8_t v_isShared_5497_; uint8_t v_isSharedCheck_5501_; 
lean_dec_ref(v_pre_5269_);
lean_dec_ref(v_info_5268_);
lean_dec(v_goal_5267_);
lean_dec_ref(v___x_5266_);
lean_dec_ref(v___x_5265_);
v_a_5494_ = lean_ctor_get(v___x_5282_, 0);
v_isSharedCheck_5501_ = !lean_is_exclusive(v___x_5282_);
if (v_isSharedCheck_5501_ == 0)
{
v___x_5496_ = v___x_5282_;
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
else
{
lean_inc(v_a_5494_);
lean_dec(v___x_5282_);
v___x_5496_ = lean_box(0);
v_isShared_5497_ = v_isSharedCheck_5501_;
goto v_resetjp_5495_;
}
v_resetjp_5495_:
{
lean_object* v___x_5499_; 
if (v_isShared_5497_ == 0)
{
v___x_5499_ = v___x_5496_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v_a_5494_);
v___x_5499_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
return v___x_5499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___boxed(lean_object** _args){
lean_object* v_scope_5502_ = _args[0];
lean_object* v___x_5503_ = _args[1];
lean_object* v___x_5504_ = _args[2];
lean_object* v_goal_5505_ = _args[3];
lean_object* v_info_5506_ = _args[4];
lean_object* v_pre_5507_ = _args[5];
lean_object* v___y_5508_ = _args[6];
lean_object* v___y_5509_ = _args[7];
lean_object* v___y_5510_ = _args[8];
lean_object* v___y_5511_ = _args[9];
lean_object* v___y_5512_ = _args[10];
lean_object* v___y_5513_ = _args[11];
lean_object* v___y_5514_ = _args[12];
lean_object* v___y_5515_ = _args[13];
lean_object* v___y_5516_ = _args[14];
lean_object* v___y_5517_ = _args[15];
lean_object* v___y_5518_ = _args[16];
lean_object* v___y_5519_ = _args[17];
_start:
{
lean_object* v_res_5520_; 
v_res_5520_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0(v_scope_5502_, v___x_5503_, v___x_5504_, v_goal_5505_, v_info_5506_, v_pre_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
lean_dec(v___y_5518_);
lean_dec_ref(v___y_5517_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec(v___y_5514_);
lean_dec_ref(v___y_5513_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec(v___y_5509_);
lean_dec_ref(v___y_5508_);
return v_res_5520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(lean_object* v_scope_5521_, lean_object* v_goal_5522_, lean_object* v_pre_5523_, lean_object* v_info_5524_, lean_object* v_a_5525_, lean_object* v_a_5526_, lean_object* v_a_5527_, lean_object* v_a_5528_, lean_object* v_a_5529_, lean_object* v_a_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_){
_start:
{
lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___f_5539_; lean_object* v___x_5540_; 
v___x_5537_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_5524_);
v___x_5538_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_5524_);
lean_inc(v_goal_5522_);
v___f_5539_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___boxed), 18, 6);
lean_closure_set(v___f_5539_, 0, v_scope_5521_);
lean_closure_set(v___f_5539_, 1, v___x_5537_);
lean_closure_set(v___f_5539_, 2, v___x_5538_);
lean_closure_set(v___f_5539_, 3, v_goal_5522_);
lean_closure_set(v___f_5539_, 4, v_info_5524_);
lean_closure_set(v___f_5539_, 5, v_pre_5523_);
v___x_5540_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5522_, v___f_5539_, v_a_5525_, v_a_5526_, v_a_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_);
return v___x_5540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___boxed(lean_object* v_scope_5541_, lean_object* v_goal_5542_, lean_object* v_pre_5543_, lean_object* v_info_5544_, lean_object* v_a_5545_, lean_object* v_a_5546_, lean_object* v_a_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_, lean_object* v_a_5553_, lean_object* v_a_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_){
_start:
{
lean_object* v_res_5557_; 
v_res_5557_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(v_scope_5541_, v_goal_5542_, v_pre_5543_, v_info_5544_, v_a_5545_, v_a_5546_, v_a_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_, v_a_5552_, v_a_5553_, v_a_5554_, v_a_5555_);
lean_dec(v_a_5555_);
lean_dec_ref(v_a_5554_);
lean_dec(v_a_5553_);
lean_dec_ref(v_a_5552_);
lean_dec(v_a_5551_);
lean_dec_ref(v_a_5550_);
lean_dec(v_a_5549_);
lean_dec_ref(v_a_5548_);
lean_dec(v_a_5547_);
lean_dec(v_a_5546_);
lean_dec_ref(v_a_5545_);
return v_res_5557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0(lean_object* v_00_u03b2_5558_, lean_object* v_m_5559_, lean_object* v_a_5560_){
_start:
{
lean_object* v___x_5561_; 
v___x_5561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(v_m_5559_, v_a_5560_);
return v___x_5561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___boxed(lean_object* v_00_u03b2_5562_, lean_object* v_m_5563_, lean_object* v_a_5564_){
_start:
{
lean_object* v_res_5565_; 
v_res_5565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0(v_00_u03b2_5562_, v_m_5563_, v_a_5564_);
lean_dec(v_a_5564_);
lean_dec_ref(v_m_5563_);
return v_res_5565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0(lean_object* v_00_u03b2_5566_, lean_object* v_a_5567_, lean_object* v_x_5568_){
_start:
{
lean_object* v___x_5569_; 
v___x_5569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(v_a_5567_, v_x_5568_);
return v___x_5569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5570_, lean_object* v_a_5571_, lean_object* v_x_5572_){
_start:
{
lean_object* v_res_5573_; 
v_res_5573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0(v_00_u03b2_5570_, v_a_5571_, v_x_5572_);
lean_dec(v_x_5572_);
lean_dec(v_a_5571_);
return v_res_5573_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5575_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_5576_ = l_Lean_stringToMessageData(v___x_5575_);
return v___x_5576_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5578_; lean_object* v___x_5579_; 
v___x_5578_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2));
v___x_5579_ = l_Lean_stringToMessageData(v___x_5578_);
return v___x_5579_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5581_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_5582_ = l_Lean_stringToMessageData(v___x_5581_);
return v___x_5582_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; 
v___x_5584_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6));
v___x_5585_ = l_Lean_stringToMessageData(v___x_5584_);
return v___x_5585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_5588_, lean_object* v_scope_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_){
_start:
{
lean_object* v_g_5603_; lean_object* v_gs_5609_; lean_object* v___y_5613_; lean_object* v___y_5614_; lean_object* v___y_5619_; lean_object* v_g_5620_; lean_object* v___y_5626_; lean_object* v_gs_5627_; lean_object* v___y_5631_; lean_object* v_g_5632_; lean_object* v___y_5633_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5657_; lean_object* v___y_5658_; lean_object* v___y_5659_; lean_object* v___y_5660_; lean_object* v___y_5661_; lean_object* v___y_5662_; lean_object* v___y_5663_; lean_object* v___y_5664_; lean_object* v___y_5665_; lean_object* v___y_5666_; lean_object* v___y_5667_; lean_object* v___y_5668_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; lean_object* v___y_5683_; lean_object* v___y_5684_; lean_object* v___y_5685_; lean_object* v___y_5686_; lean_object* v___y_5687_; lean_object* v___y_5688_; lean_object* v___y_5689_; lean_object* v___y_5690_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___x_5807_; 
v___x_5807_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_5591_);
if (lean_obj_tag(v___x_5807_) == 0)
{
lean_object* v_a_5808_; lean_object* v___x_5810_; uint8_t v_isShared_5811_; uint8_t v_isSharedCheck_6059_; 
v_a_5808_ = lean_ctor_get(v___x_5807_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_5810_ = v___x_5807_;
v_isShared_5811_ = v_isSharedCheck_6059_;
goto v_resetjp_5809_;
}
else
{
lean_inc(v_a_5808_);
lean_dec(v___x_5807_);
v___x_5810_ = lean_box(0);
v_isShared_5811_ = v_isSharedCheck_6059_;
goto v_resetjp_5809_;
}
v_resetjp_5809_:
{
uint8_t v___x_5812_; 
v___x_5812_ = lean_unbox(v_a_5808_);
lean_dec(v_a_5808_);
if (v___x_5812_ == 0)
{
lean_object* v___x_5813_; 
lean_del_object(v___x_5810_);
lean_inc(v_goal_5588_);
v___x_5813_ = l_Lean_MVarId_getType(v_goal_5588_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_);
if (lean_obj_tag(v___x_5813_) == 0)
{
lean_object* v_a_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_6046_; 
v_a_5814_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_6046_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_6046_ == 0)
{
v___x_5816_ = v___x_5813_;
v_isShared_5817_ = v_isSharedCheck_6046_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_a_5814_);
lean_dec(v___x_5813_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_6046_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v_options_5824_; lean_object* v_inheritedTraceOptions_5825_; uint8_t v_hasTrace_5826_; lean_object* v___x_5827_; lean_object* v___y_5829_; lean_object* v___y_5830_; lean_object* v___y_5831_; lean_object* v___y_5832_; lean_object* v___y_5833_; lean_object* v___y_5834_; lean_object* v___y_5835_; lean_object* v___y_5836_; lean_object* v___y_5837_; lean_object* v___y_5838_; lean_object* v___y_5839_; 
v_options_5824_ = lean_ctor_get(v___y_5599_, 2);
v_inheritedTraceOptions_5825_ = lean_ctor_get(v___y_5599_, 13);
v_hasTrace_5826_ = lean_ctor_get_uint8(v_options_5824_, sizeof(void*)*1);
v___x_5827_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_5826_ == 0)
{
v___y_5829_ = v___y_5590_;
v___y_5830_ = v___y_5591_;
v___y_5831_ = v___y_5592_;
v___y_5832_ = v___y_5593_;
v___y_5833_ = v___y_5594_;
v___y_5834_ = v___y_5595_;
v___y_5835_ = v___y_5596_;
v___y_5836_ = v___y_5597_;
v___y_5837_ = v___y_5598_;
v___y_5838_ = v___y_5599_;
v___y_5839_ = v___y_5600_;
goto v___jp_5828_;
}
else
{
lean_object* v___x_6032_; uint8_t v___x_6033_; 
v___x_6032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_6033_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5825_, v_options_5824_, v___x_6032_);
if (v___x_6033_ == 0)
{
v___y_5829_ = v___y_5590_;
v___y_5830_ = v___y_5591_;
v___y_5831_ = v___y_5592_;
v___y_5832_ = v___y_5593_;
v___y_5833_ = v___y_5594_;
v___y_5834_ = v___y_5595_;
v___y_5835_ = v___y_5596_;
v___y_5836_ = v___y_5597_;
v___y_5837_ = v___y_5598_;
v___y_5838_ = v___y_5599_;
v___y_5839_ = v___y_5600_;
goto v___jp_5828_;
}
else
{
lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; 
v___x_6034_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_5814_);
v___x_6035_ = l_Lean_MessageData_ofExpr(v_a_5814_);
v___x_6036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6034_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5827_, v___x_6036_, v___y_5597_, v___y_5598_, v___y_5599_, v___y_5600_);
if (lean_obj_tag(v___x_6037_) == 0)
{
lean_dec_ref_known(v___x_6037_, 1);
v___y_5829_ = v___y_5590_;
v___y_5830_ = v___y_5591_;
v___y_5831_ = v___y_5592_;
v___y_5832_ = v___y_5593_;
v___y_5833_ = v___y_5594_;
v___y_5834_ = v___y_5595_;
v___y_5835_ = v___y_5596_;
v___y_5836_ = v___y_5597_;
v___y_5837_ = v___y_5598_;
v___y_5838_ = v___y_5599_;
v___y_5839_ = v___y_5600_;
goto v___jp_5828_;
}
else
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6045_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6038_ = lean_ctor_get(v___x_6037_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_6037_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6040_ = v___x_6037_;
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_6037_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6043_; 
if (v_isShared_6041_ == 0)
{
v___x_6043_ = v___x_6040_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_a_6038_);
v___x_6043_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
return v___x_6043_;
}
}
}
}
}
v___jp_5818_:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5822_; 
v___x_5819_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5819_, 0, v_a_5814_);
v___x_5820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5820_, 0, v___x_5819_);
if (v_isShared_5817_ == 0)
{
lean_ctor_set(v___x_5816_, 0, v___x_5820_);
v___x_5822_ = v___x_5816_;
goto v_reusejp_5821_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v___x_5820_);
v___x_5822_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5821_;
}
v_reusejp_5821_:
{
return v___x_5822_;
}
}
v___jp_5828_:
{
lean_object* v___x_5840_; 
lean_inc(v_goal_5588_);
v___x_5840_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_5588_, v_a_5814_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5840_) == 0)
{
lean_object* v_a_5841_; 
v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
lean_inc(v_a_5841_);
lean_dec_ref_known(v___x_5840_, 1);
if (lean_obj_tag(v_a_5841_) == 1)
{
lean_object* v_val_5842_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_val_5842_ = lean_ctor_get(v_a_5841_, 0);
lean_inc(v_val_5842_);
lean_dec_ref_known(v_a_5841_, 1);
v_gs_5609_ = v_val_5842_;
goto v___jp_5608_;
}
else
{
lean_object* v___x_5843_; 
lean_dec(v_a_5841_);
lean_inc(v_a_5814_);
lean_inc(v_goal_5588_);
v___x_5843_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_5588_, v_a_5814_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5843_) == 0)
{
lean_object* v_a_5844_; 
v_a_5844_ = lean_ctor_get(v___x_5843_, 0);
lean_inc(v_a_5844_);
lean_dec_ref_known(v___x_5843_, 1);
if (lean_obj_tag(v_a_5844_) == 1)
{
lean_object* v_val_5845_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_val_5845_ = lean_ctor_get(v_a_5844_, 0);
lean_inc(v_val_5845_);
lean_dec_ref_known(v_a_5844_, 1);
v_g_5603_ = v_val_5845_;
goto v___jp_5602_;
}
else
{
lean_object* v___x_5846_; 
lean_dec(v_a_5844_);
lean_inc(v_goal_5588_);
v___x_5846_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_5588_, v_a_5814_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5846_) == 0)
{
lean_object* v_a_5847_; 
v_a_5847_ = lean_ctor_get(v___x_5846_, 0);
lean_inc(v_a_5847_);
lean_dec_ref_known(v___x_5846_, 1);
if (lean_obj_tag(v_a_5847_) == 1)
{
lean_object* v_val_5848_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_val_5848_ = lean_ctor_get(v_a_5847_, 0);
lean_inc(v_val_5848_);
lean_dec_ref_known(v_a_5847_, 1);
v_g_5603_ = v_val_5848_;
goto v___jp_5602_;
}
else
{
lean_object* v___x_5849_; 
lean_dec(v_a_5847_);
lean_inc(v_a_5814_);
lean_inc(v_goal_5588_);
v___x_5849_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_5588_, v_a_5814_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5850_);
lean_dec_ref_known(v___x_5849_, 1);
if (lean_obj_tag(v_a_5850_) == 1)
{
lean_object* v_val_5851_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_val_5851_ = lean_ctor_get(v_a_5850_, 0);
lean_inc(v_val_5851_);
lean_dec_ref_known(v_a_5850_, 1);
v_g_5603_ = v_val_5851_;
goto v___jp_5602_;
}
else
{
lean_object* v___x_5852_; 
lean_dec(v_a_5850_);
lean_inc(v_a_5814_);
lean_inc(v_goal_5588_);
lean_inc_ref(v_scope_5589_);
v___x_5852_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_5589_, v_goal_5588_, v_a_5814_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_a_5853_; 
v_a_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5853_);
lean_dec_ref_known(v___x_5852_, 1);
if (lean_obj_tag(v_a_5853_) == 1)
{
lean_object* v_val_5854_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_val_5854_ = lean_ctor_get(v_a_5853_, 0);
lean_inc(v_val_5854_);
lean_dec_ref_known(v_a_5853_, 1);
v_gs_5609_ = v_val_5854_;
goto v___jp_5608_;
}
else
{
lean_object* v___x_5855_; uint8_t v___x_5856_; 
lean_dec(v_a_5853_);
lean_inc(v_a_5814_);
v___x_5855_ = l_Lean_Expr_cleanupAnnotations(v_a_5814_);
v___x_5856_ = l_Lean_Expr_isApp(v___x_5855_);
if (v___x_5856_ == 0)
{
lean_dec_ref(v___x_5855_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
goto v___jp_5818_;
}
else
{
lean_object* v_arg_5857_; lean_object* v___x_5858_; uint8_t v___x_5859_; 
v_arg_5857_ = lean_ctor_get(v___x_5855_, 1);
lean_inc_ref(v_arg_5857_);
v___x_5858_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5855_);
v___x_5859_ = l_Lean_Expr_isApp(v___x_5858_);
if (v___x_5859_ == 0)
{
lean_dec_ref(v___x_5858_);
lean_dec_ref(v_arg_5857_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
goto v___jp_5818_;
}
else
{
lean_object* v_arg_5860_; lean_object* v___x_5861_; uint8_t v___x_5862_; 
v_arg_5860_ = lean_ctor_get(v___x_5858_, 1);
lean_inc_ref(v_arg_5860_);
v___x_5861_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5858_);
v___x_5862_ = l_Lean_Expr_isApp(v___x_5861_);
if (v___x_5862_ == 0)
{
lean_dec_ref(v___x_5861_);
lean_dec_ref(v_arg_5860_);
lean_dec_ref(v_arg_5857_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
goto v___jp_5818_;
}
else
{
lean_object* v_arg_5863_; lean_object* v___x_5864_; uint8_t v___x_5865_; 
v_arg_5863_ = lean_ctor_get(v___x_5861_, 1);
lean_inc_ref(v_arg_5863_);
v___x_5864_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5861_);
v___x_5865_ = l_Lean_Expr_isApp(v___x_5864_);
if (v___x_5865_ == 0)
{
lean_dec_ref(v___x_5864_);
lean_dec_ref(v_arg_5863_);
lean_dec_ref(v_arg_5860_);
lean_dec_ref(v_arg_5857_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
goto v___jp_5818_;
}
else
{
lean_object* v_arg_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; uint8_t v___x_5869_; 
v_arg_5866_ = lean_ctor_get(v___x_5864_, 1);
lean_inc_ref(v_arg_5866_);
v___x_5867_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5864_);
v___x_5868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5869_ = l_Lean_Expr_isConstOf(v___x_5867_, v___x_5868_);
lean_dec_ref(v___x_5867_);
if (v___x_5869_ == 0)
{
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec_ref(v_arg_5860_);
lean_dec_ref(v_arg_5857_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
goto v___jp_5818_;
}
else
{
lean_object* v___x_5870_; 
lean_del_object(v___x_5816_);
v___x_5870_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_5860_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5870_) == 0)
{
lean_object* v_a_5871_; lean_object* v___x_5872_; 
v_a_5871_ = lean_ctor_get(v___x_5870_, 0);
lean_inc(v_a_5871_);
lean_dec_ref_known(v___x_5870_, 1);
v___x_5872_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_5857_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5872_) == 0)
{
lean_object* v_a_5873_; lean_object* v___x_5874_; 
v_a_5873_ = lean_ctor_get(v___x_5872_, 0);
lean_inc(v_a_5873_);
lean_dec_ref_known(v___x_5872_, 1);
lean_inc(v_goal_5588_);
v___x_5874_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_5588_, v___y_5829_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5874_) == 0)
{
lean_object* v_a_5875_; 
v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5875_);
lean_dec_ref_known(v___x_5874_, 1);
if (lean_obj_tag(v_a_5875_) == 1)
{
lean_object* v_val_5876_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_val_5876_ = lean_ctor_get(v_a_5875_, 0);
lean_inc(v_val_5876_);
lean_dec_ref_known(v_a_5875_, 1);
v_gs_5609_ = v_val_5876_;
goto v___jp_5608_;
}
else
{
lean_object* v___x_5877_; 
lean_dec(v_a_5875_);
lean_inc(v_a_5814_);
lean_inc(v_a_5871_);
lean_inc(v_goal_5588_);
lean_inc_ref(v_scope_5589_);
v___x_5877_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_5589_, v_goal_5588_, v_arg_5866_, v_a_5871_, v_a_5814_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5877_) == 0)
{
lean_object* v_a_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5959_; 
v_a_5878_ = lean_ctor_get(v___x_5877_, 0);
v_isSharedCheck_5959_ = !lean_is_exclusive(v___x_5877_);
if (v_isSharedCheck_5959_ == 0)
{
v___x_5880_ = v___x_5877_;
v_isShared_5881_ = v_isSharedCheck_5959_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_a_5878_);
lean_dec(v___x_5877_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5959_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
if (lean_obj_tag(v_a_5878_) == 1)
{
lean_object* v_val_5882_; lean_object* v_fst_5883_; lean_object* v_snd_5884_; lean_object* v___x_5886_; uint8_t v_isShared_5887_; uint8_t v_isSharedCheck_5894_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_val_5882_ = lean_ctor_get(v_a_5878_, 0);
lean_inc(v_val_5882_);
lean_dec_ref_known(v_a_5878_, 1);
v_fst_5883_ = lean_ctor_get(v_val_5882_, 0);
v_snd_5884_ = lean_ctor_get(v_val_5882_, 1);
v_isSharedCheck_5894_ = !lean_is_exclusive(v_val_5882_);
if (v_isSharedCheck_5894_ == 0)
{
v___x_5886_ = v_val_5882_;
v_isShared_5887_ = v_isSharedCheck_5894_;
goto v_resetjp_5885_;
}
else
{
lean_inc(v_snd_5884_);
lean_inc(v_fst_5883_);
lean_dec(v_val_5882_);
v___x_5886_ = lean_box(0);
v_isShared_5887_ = v_isSharedCheck_5894_;
goto v_resetjp_5885_;
}
v_resetjp_5885_:
{
lean_object* v___x_5889_; 
if (v_isShared_5887_ == 0)
{
v___x_5889_ = v___x_5886_;
goto v_reusejp_5888_;
}
else
{
lean_object* v_reuseFailAlloc_5893_; 
v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_fst_5883_);
lean_ctor_set(v_reuseFailAlloc_5893_, 1, v_snd_5884_);
v___x_5889_ = v_reuseFailAlloc_5893_;
goto v_reusejp_5888_;
}
v_reusejp_5888_:
{
lean_object* v___x_5891_; 
if (v_isShared_5881_ == 0)
{
lean_ctor_set(v___x_5880_, 0, v___x_5889_);
v___x_5891_ = v___x_5880_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v___x_5889_);
v___x_5891_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
return v___x_5891_;
}
}
}
}
else
{
lean_object* v___x_5895_; 
lean_del_object(v___x_5880_);
lean_dec(v_a_5878_);
lean_inc(v_goal_5588_);
v___x_5895_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_5589_, v_goal_5588_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v_a_5896_; lean_object* v___x_5897_; 
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
lean_inc(v_a_5896_);
lean_dec_ref_known(v___x_5895_, 1);
lean_inc(v_a_5873_);
lean_inc(v_a_5871_);
lean_inc_ref(v_arg_5866_);
lean_inc(v_goal_5588_);
v___x_5897_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_5588_, v_a_5814_, v_arg_5866_, v_arg_5863_, v_a_5871_, v_a_5873_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_object* v_a_5898_; 
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_a_5898_);
lean_dec_ref_known(v___x_5897_, 1);
if (lean_obj_tag(v_a_5898_) == 1)
{
lean_object* v_val_5899_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec(v_goal_5588_);
v_val_5899_ = lean_ctor_get(v_a_5898_, 0);
lean_inc(v_val_5899_);
lean_dec_ref_known(v_a_5898_, 1);
v___y_5619_ = v_a_5896_;
v_g_5620_ = v_val_5899_;
goto v___jp_5618_;
}
else
{
lean_object* v___x_5900_; 
lean_dec(v_a_5898_);
lean_inc(v_a_5873_);
lean_inc(v_goal_5588_);
v___x_5900_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_5588_, v_a_5873_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
lean_inc(v_a_5901_);
lean_dec_ref_known(v___x_5900_, 1);
if (lean_obj_tag(v_a_5901_) == 1)
{
lean_object* v_val_5902_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec(v_goal_5588_);
v_val_5902_ = lean_ctor_get(v_a_5901_, 0);
lean_inc(v_val_5902_);
lean_dec_ref_known(v_a_5901_, 1);
v___y_5626_ = v_a_5896_;
v_gs_5627_ = v_val_5902_;
goto v___jp_5625_;
}
else
{
lean_object* v___x_5903_; 
lean_dec(v_a_5901_);
lean_inc(v_a_5873_);
lean_inc(v_a_5871_);
lean_inc(v_goal_5588_);
lean_inc(v_a_5896_);
v___x_5903_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_a_5896_, v_goal_5588_, v_arg_5866_, v_a_5871_, v_a_5873_, v___y_5829_, v___y_5830_, v___y_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
lean_dec_ref(v_arg_5866_);
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v_a_5904_; 
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
lean_inc(v_a_5904_);
lean_dec_ref_known(v___x_5903_, 1);
if (lean_obj_tag(v_a_5904_) == 1)
{
lean_object* v_val_5905_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec(v_goal_5588_);
v_val_5905_ = lean_ctor_get(v_a_5904_, 0);
lean_inc(v_val_5905_);
lean_dec_ref_known(v_a_5904_, 1);
v___y_5626_ = v_a_5896_;
v_gs_5627_ = v_val_5905_;
goto v___jp_5625_;
}
else
{
lean_object* v___x_5906_; 
lean_dec(v_a_5904_);
lean_inc(v_a_5873_);
v___x_5906_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(v_a_5873_);
if (lean_obj_tag(v___x_5906_) == 1)
{
lean_object* v_options_5907_; uint8_t v_hasTrace_5908_; 
v_options_5907_ = lean_ctor_get(v___y_5838_, 2);
v_hasTrace_5908_ = lean_ctor_get_uint8(v_options_5907_, sizeof(void*)*1);
if (v_hasTrace_5908_ == 0)
{
lean_object* v_val_5909_; 
v_val_5909_ = lean_ctor_get(v___x_5906_, 0);
lean_inc(v_val_5909_);
lean_dec_ref_known(v___x_5906_, 1);
v___y_5680_ = v_a_5871_;
v___y_5681_ = v_val_5909_;
v___y_5682_ = v_a_5896_;
v___y_5683_ = v_a_5873_;
v___y_5684_ = v___y_5829_;
v___y_5685_ = v___y_5830_;
v___y_5686_ = v___y_5831_;
v___y_5687_ = v___y_5832_;
v___y_5688_ = v___y_5833_;
v___y_5689_ = v___y_5834_;
v___y_5690_ = v___y_5835_;
v___y_5691_ = v___y_5836_;
v___y_5692_ = v___y_5837_;
v___y_5693_ = v___y_5838_;
v___y_5694_ = v___y_5839_;
goto v___jp_5679_;
}
else
{
lean_object* v_val_5910_; lean_object* v_inheritedTraceOptions_5911_; lean_object* v___x_5912_; uint8_t v___x_5913_; 
v_val_5910_ = lean_ctor_get(v___x_5906_, 0);
lean_inc(v_val_5910_);
lean_dec_ref_known(v___x_5906_, 1);
v_inheritedTraceOptions_5911_ = lean_ctor_get(v___y_5838_, 13);
v___x_5912_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5913_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5911_, v_options_5907_, v___x_5912_);
if (v___x_5913_ == 0)
{
v___y_5680_ = v_a_5871_;
v___y_5681_ = v_val_5910_;
v___y_5682_ = v_a_5896_;
v___y_5683_ = v_a_5873_;
v___y_5684_ = v___y_5829_;
v___y_5685_ = v___y_5830_;
v___y_5686_ = v___y_5831_;
v___y_5687_ = v___y_5832_;
v___y_5688_ = v___y_5833_;
v___y_5689_ = v___y_5834_;
v___y_5690_ = v___y_5835_;
v___y_5691_ = v___y_5836_;
v___y_5692_ = v___y_5837_;
v___y_5693_ = v___y_5838_;
v___y_5694_ = v___y_5839_;
goto v___jp_5679_;
}
else
{
lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; 
v___x_5914_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5);
v___x_5915_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_val_5910_);
v___x_5916_ = l_Lean_MessageData_ofExpr(v___x_5915_);
v___x_5917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5914_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
v___x_5918_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5827_, v___x_5917_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
if (lean_obj_tag(v___x_5918_) == 0)
{
lean_dec_ref_known(v___x_5918_, 1);
v___y_5680_ = v_a_5871_;
v___y_5681_ = v_val_5910_;
v___y_5682_ = v_a_5896_;
v___y_5683_ = v_a_5873_;
v___y_5684_ = v___y_5829_;
v___y_5685_ = v___y_5830_;
v___y_5686_ = v___y_5831_;
v___y_5687_ = v___y_5832_;
v___y_5688_ = v___y_5833_;
v___y_5689_ = v___y_5834_;
v___y_5690_ = v___y_5835_;
v___y_5691_ = v___y_5836_;
v___y_5692_ = v___y_5837_;
v___y_5693_ = v___y_5838_;
v___y_5694_ = v___y_5839_;
goto v___jp_5679_;
}
else
{
lean_object* v_a_5919_; lean_object* v___x_5921_; uint8_t v_isShared_5922_; uint8_t v_isSharedCheck_5926_; 
lean_dec(v_val_5910_);
lean_dec(v_a_5896_);
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec(v_goal_5588_);
v_a_5919_ = lean_ctor_get(v___x_5918_, 0);
v_isSharedCheck_5926_ = !lean_is_exclusive(v___x_5918_);
if (v_isSharedCheck_5926_ == 0)
{
v___x_5921_ = v___x_5918_;
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
else
{
lean_inc(v_a_5919_);
lean_dec(v___x_5918_);
v___x_5921_ = lean_box(0);
v_isShared_5922_ = v_isSharedCheck_5926_;
goto v_resetjp_5920_;
}
v_resetjp_5920_:
{
lean_object* v___x_5924_; 
if (v_isShared_5922_ == 0)
{
v___x_5924_ = v___x_5921_;
goto v_reusejp_5923_;
}
else
{
lean_object* v_reuseFailAlloc_5925_; 
v_reuseFailAlloc_5925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5919_);
v___x_5924_ = v_reuseFailAlloc_5925_;
goto v_reusejp_5923_;
}
v_reusejp_5923_:
{
return v___x_5924_;
}
}
}
}
}
}
else
{
lean_dec(v___x_5906_);
lean_dec(v_a_5896_);
lean_dec(v_goal_5588_);
v___y_5613_ = v_a_5871_;
v___y_5614_ = v_a_5873_;
goto v___jp_5612_;
}
}
}
else
{
lean_object* v_a_5927_; lean_object* v___x_5929_; uint8_t v_isShared_5930_; uint8_t v_isSharedCheck_5934_; 
lean_dec(v_a_5896_);
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec(v_goal_5588_);
v_a_5927_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5934_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5934_ == 0)
{
v___x_5929_ = v___x_5903_;
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
else
{
lean_inc(v_a_5927_);
lean_dec(v___x_5903_);
v___x_5929_ = lean_box(0);
v_isShared_5930_ = v_isSharedCheck_5934_;
goto v_resetjp_5928_;
}
v_resetjp_5928_:
{
lean_object* v___x_5932_; 
if (v_isShared_5930_ == 0)
{
v___x_5932_ = v___x_5929_;
goto v_reusejp_5931_;
}
else
{
lean_object* v_reuseFailAlloc_5933_; 
v_reuseFailAlloc_5933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5933_, 0, v_a_5927_);
v___x_5932_ = v_reuseFailAlloc_5933_;
goto v_reusejp_5931_;
}
v_reusejp_5931_:
{
return v___x_5932_;
}
}
}
}
}
else
{
lean_object* v_a_5935_; lean_object* v___x_5937_; uint8_t v_isShared_5938_; uint8_t v_isSharedCheck_5942_; 
lean_dec(v_a_5896_);
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec(v_goal_5588_);
v_a_5935_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_5942_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_5942_ == 0)
{
v___x_5937_ = v___x_5900_;
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
else
{
lean_inc(v_a_5935_);
lean_dec(v___x_5900_);
v___x_5937_ = lean_box(0);
v_isShared_5938_ = v_isSharedCheck_5942_;
goto v_resetjp_5936_;
}
v_resetjp_5936_:
{
lean_object* v___x_5940_; 
if (v_isShared_5938_ == 0)
{
v___x_5940_ = v___x_5937_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5941_; 
v_reuseFailAlloc_5941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5941_, 0, v_a_5935_);
v___x_5940_ = v_reuseFailAlloc_5941_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
return v___x_5940_;
}
}
}
}
}
else
{
lean_object* v_a_5943_; lean_object* v___x_5945_; uint8_t v_isShared_5946_; uint8_t v_isSharedCheck_5950_; 
lean_dec(v_a_5896_);
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec(v_goal_5588_);
v_a_5943_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5950_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5950_ == 0)
{
v___x_5945_ = v___x_5897_;
v_isShared_5946_ = v_isSharedCheck_5950_;
goto v_resetjp_5944_;
}
else
{
lean_inc(v_a_5943_);
lean_dec(v___x_5897_);
v___x_5945_ = lean_box(0);
v_isShared_5946_ = v_isSharedCheck_5950_;
goto v_resetjp_5944_;
}
v_resetjp_5944_:
{
lean_object* v___x_5948_; 
if (v_isShared_5946_ == 0)
{
v___x_5948_ = v___x_5945_;
goto v_reusejp_5947_;
}
else
{
lean_object* v_reuseFailAlloc_5949_; 
v_reuseFailAlloc_5949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5949_, 0, v_a_5943_);
v___x_5948_ = v_reuseFailAlloc_5949_;
goto v_reusejp_5947_;
}
v_reusejp_5947_:
{
return v___x_5948_;
}
}
}
}
else
{
lean_object* v_a_5951_; lean_object* v___x_5953_; uint8_t v_isShared_5954_; uint8_t v_isSharedCheck_5958_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec(v_a_5814_);
lean_dec(v_goal_5588_);
v_a_5951_ = lean_ctor_get(v___x_5895_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5895_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5953_ = v___x_5895_;
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
else
{
lean_inc(v_a_5951_);
lean_dec(v___x_5895_);
v___x_5953_ = lean_box(0);
v_isShared_5954_ = v_isSharedCheck_5958_;
goto v_resetjp_5952_;
}
v_resetjp_5952_:
{
lean_object* v___x_5956_; 
if (v_isShared_5954_ == 0)
{
v___x_5956_ = v___x_5953_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v_a_5951_);
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
}
}
else
{
lean_object* v_a_5960_; lean_object* v___x_5962_; uint8_t v_isShared_5963_; uint8_t v_isSharedCheck_5967_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_5960_ = lean_ctor_get(v___x_5877_, 0);
v_isSharedCheck_5967_ = !lean_is_exclusive(v___x_5877_);
if (v_isSharedCheck_5967_ == 0)
{
v___x_5962_ = v___x_5877_;
v_isShared_5963_ = v_isSharedCheck_5967_;
goto v_resetjp_5961_;
}
else
{
lean_inc(v_a_5960_);
lean_dec(v___x_5877_);
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
}
else
{
lean_object* v_a_5968_; lean_object* v___x_5970_; uint8_t v_isShared_5971_; uint8_t v_isSharedCheck_5975_; 
lean_dec(v_a_5873_);
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_5968_ = lean_ctor_get(v___x_5874_, 0);
v_isSharedCheck_5975_ = !lean_is_exclusive(v___x_5874_);
if (v_isSharedCheck_5975_ == 0)
{
v___x_5970_ = v___x_5874_;
v_isShared_5971_ = v_isSharedCheck_5975_;
goto v_resetjp_5969_;
}
else
{
lean_inc(v_a_5968_);
lean_dec(v___x_5874_);
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
else
{
lean_object* v_a_5976_; lean_object* v___x_5978_; uint8_t v_isShared_5979_; uint8_t v_isSharedCheck_5983_; 
lean_dec(v_a_5871_);
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_5976_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_5983_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_5983_ == 0)
{
v___x_5978_ = v___x_5872_;
v_isShared_5979_ = v_isSharedCheck_5983_;
goto v_resetjp_5977_;
}
else
{
lean_inc(v_a_5976_);
lean_dec(v___x_5872_);
v___x_5978_ = lean_box(0);
v_isShared_5979_ = v_isSharedCheck_5983_;
goto v_resetjp_5977_;
}
v_resetjp_5977_:
{
lean_object* v___x_5981_; 
if (v_isShared_5979_ == 0)
{
v___x_5981_ = v___x_5978_;
goto v_reusejp_5980_;
}
else
{
lean_object* v_reuseFailAlloc_5982_; 
v_reuseFailAlloc_5982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5982_, 0, v_a_5976_);
v___x_5981_ = v_reuseFailAlloc_5982_;
goto v_reusejp_5980_;
}
v_reusejp_5980_:
{
return v___x_5981_;
}
}
}
}
else
{
lean_object* v_a_5984_; lean_object* v___x_5986_; uint8_t v_isShared_5987_; uint8_t v_isSharedCheck_5991_; 
lean_dec_ref(v_arg_5866_);
lean_dec_ref(v_arg_5863_);
lean_dec_ref(v_arg_5857_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_5984_ = lean_ctor_get(v___x_5870_, 0);
v_isSharedCheck_5991_ = !lean_is_exclusive(v___x_5870_);
if (v_isSharedCheck_5991_ == 0)
{
v___x_5986_ = v___x_5870_;
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
else
{
lean_inc(v_a_5984_);
lean_dec(v___x_5870_);
v___x_5986_ = lean_box(0);
v_isShared_5987_ = v_isSharedCheck_5991_;
goto v_resetjp_5985_;
}
v_resetjp_5985_:
{
lean_object* v___x_5989_; 
if (v_isShared_5987_ == 0)
{
v___x_5989_ = v___x_5986_;
goto v_reusejp_5988_;
}
else
{
lean_object* v_reuseFailAlloc_5990_; 
v_reuseFailAlloc_5990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_a_5984_);
v___x_5989_ = v_reuseFailAlloc_5990_;
goto v_reusejp_5988_;
}
v_reusejp_5988_:
{
return v___x_5989_;
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
lean_object* v_a_5992_; lean_object* v___x_5994_; uint8_t v_isShared_5995_; uint8_t v_isSharedCheck_5999_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_5992_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5999_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5999_ == 0)
{
v___x_5994_ = v___x_5852_;
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
else
{
lean_inc(v_a_5992_);
lean_dec(v___x_5852_);
v___x_5994_ = lean_box(0);
v_isShared_5995_ = v_isSharedCheck_5999_;
goto v_resetjp_5993_;
}
v_resetjp_5993_:
{
lean_object* v___x_5997_; 
if (v_isShared_5995_ == 0)
{
v___x_5997_ = v___x_5994_;
goto v_reusejp_5996_;
}
else
{
lean_object* v_reuseFailAlloc_5998_; 
v_reuseFailAlloc_5998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5998_, 0, v_a_5992_);
v___x_5997_ = v_reuseFailAlloc_5998_;
goto v_reusejp_5996_;
}
v_reusejp_5996_:
{
return v___x_5997_;
}
}
}
}
}
else
{
lean_object* v_a_6000_; lean_object* v___x_6002_; uint8_t v_isShared_6003_; uint8_t v_isSharedCheck_6007_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6000_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_6007_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_6007_ == 0)
{
v___x_6002_ = v___x_5849_;
v_isShared_6003_ = v_isSharedCheck_6007_;
goto v_resetjp_6001_;
}
else
{
lean_inc(v_a_6000_);
lean_dec(v___x_5849_);
v___x_6002_ = lean_box(0);
v_isShared_6003_ = v_isSharedCheck_6007_;
goto v_resetjp_6001_;
}
v_resetjp_6001_:
{
lean_object* v___x_6005_; 
if (v_isShared_6003_ == 0)
{
v___x_6005_ = v___x_6002_;
goto v_reusejp_6004_;
}
else
{
lean_object* v_reuseFailAlloc_6006_; 
v_reuseFailAlloc_6006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_a_6000_);
v___x_6005_ = v_reuseFailAlloc_6006_;
goto v_reusejp_6004_;
}
v_reusejp_6004_:
{
return v___x_6005_;
}
}
}
}
}
else
{
lean_object* v_a_6008_; lean_object* v___x_6010_; uint8_t v_isShared_6011_; uint8_t v_isSharedCheck_6015_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6008_ = lean_ctor_get(v___x_5846_, 0);
v_isSharedCheck_6015_ = !lean_is_exclusive(v___x_5846_);
if (v_isSharedCheck_6015_ == 0)
{
v___x_6010_ = v___x_5846_;
v_isShared_6011_ = v_isSharedCheck_6015_;
goto v_resetjp_6009_;
}
else
{
lean_inc(v_a_6008_);
lean_dec(v___x_5846_);
v___x_6010_ = lean_box(0);
v_isShared_6011_ = v_isSharedCheck_6015_;
goto v_resetjp_6009_;
}
v_resetjp_6009_:
{
lean_object* v___x_6013_; 
if (v_isShared_6011_ == 0)
{
v___x_6013_ = v___x_6010_;
goto v_reusejp_6012_;
}
else
{
lean_object* v_reuseFailAlloc_6014_; 
v_reuseFailAlloc_6014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6014_, 0, v_a_6008_);
v___x_6013_ = v_reuseFailAlloc_6014_;
goto v_reusejp_6012_;
}
v_reusejp_6012_:
{
return v___x_6013_;
}
}
}
}
}
else
{
lean_object* v_a_6016_; lean_object* v___x_6018_; uint8_t v_isShared_6019_; uint8_t v_isSharedCheck_6023_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6016_ = lean_ctor_get(v___x_5843_, 0);
v_isSharedCheck_6023_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_6023_ == 0)
{
v___x_6018_ = v___x_5843_;
v_isShared_6019_ = v_isSharedCheck_6023_;
goto v_resetjp_6017_;
}
else
{
lean_inc(v_a_6016_);
lean_dec(v___x_5843_);
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
}
else
{
lean_object* v_a_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6031_; 
lean_del_object(v___x_5816_);
lean_dec(v_a_5814_);
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6024_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_6031_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_6031_ == 0)
{
v___x_6026_ = v___x_5840_;
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_a_6024_);
lean_dec(v___x_5840_);
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
}
}
else
{
lean_object* v_a_6047_; lean_object* v___x_6049_; uint8_t v_isShared_6050_; uint8_t v_isSharedCheck_6054_; 
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6047_ = lean_ctor_get(v___x_5813_, 0);
v_isSharedCheck_6054_ = !lean_is_exclusive(v___x_5813_);
if (v_isSharedCheck_6054_ == 0)
{
v___x_6049_ = v___x_5813_;
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
else
{
lean_inc(v_a_6047_);
lean_dec(v___x_5813_);
v___x_6049_ = lean_box(0);
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
v_resetjp_6048_:
{
lean_object* v___x_6052_; 
if (v_isShared_6050_ == 0)
{
v___x_6052_ = v___x_6049_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_a_6047_);
v___x_6052_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
return v___x_6052_;
}
}
}
}
else
{
lean_object* v___x_6055_; lean_object* v___x_6057_; 
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v___x_6055_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
if (v_isShared_5811_ == 0)
{
lean_ctor_set(v___x_5810_, 0, v___x_6055_);
v___x_6057_ = v___x_5810_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v___x_6055_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
else
{
lean_object* v_a_6060_; lean_object* v___x_6062_; uint8_t v_isShared_6063_; uint8_t v_isSharedCheck_6067_; 
lean_dec_ref(v_scope_5589_);
lean_dec(v_goal_5588_);
v_a_6060_ = lean_ctor_get(v___x_5807_, 0);
v_isSharedCheck_6067_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_6067_ == 0)
{
v___x_6062_ = v___x_5807_;
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
else
{
lean_inc(v_a_6060_);
lean_dec(v___x_5807_);
v___x_6062_ = lean_box(0);
v_isShared_6063_ = v_isSharedCheck_6067_;
goto v_resetjp_6061_;
}
v_resetjp_6061_:
{
lean_object* v___x_6065_; 
if (v_isShared_6063_ == 0)
{
v___x_6065_ = v___x_6062_;
goto v_reusejp_6064_;
}
else
{
lean_object* v_reuseFailAlloc_6066_; 
v_reuseFailAlloc_6066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6066_, 0, v_a_6060_);
v___x_6065_ = v_reuseFailAlloc_6066_;
goto v_reusejp_6064_;
}
v_reusejp_6064_:
{
return v___x_6065_;
}
}
}
v___jp_5602_:
{
lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; 
v___x_5604_ = lean_box(0);
v___x_5605_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5605_, 0, v_g_5603_);
lean_ctor_set(v___x_5605_, 1, v___x_5604_);
v___x_5606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5606_, 0, v_scope_5589_);
lean_ctor_set(v___x_5606_, 1, v___x_5605_);
v___x_5607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5607_, 0, v___x_5606_);
return v___x_5607_;
}
v___jp_5608_:
{
lean_object* v___x_5610_; lean_object* v___x_5611_; 
v___x_5610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5610_, 0, v_scope_5589_);
lean_ctor_set(v___x_5610_, 1, v_gs_5609_);
v___x_5611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5611_, 0, v___x_5610_);
return v___x_5611_;
}
v___jp_5612_:
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v___x_5615_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___y_5613_);
lean_ctor_set(v___x_5615_, 1, v___y_5614_);
v___x_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5615_);
v___x_5617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5616_);
return v___x_5617_;
}
v___jp_5618_:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v___x_5621_ = lean_box(0);
v___x_5622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5622_, 0, v_g_5620_);
lean_ctor_set(v___x_5622_, 1, v___x_5621_);
v___x_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___y_5619_);
lean_ctor_set(v___x_5623_, 1, v___x_5622_);
v___x_5624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5623_);
return v___x_5624_;
}
v___jp_5625_:
{
lean_object* v___x_5628_; lean_object* v___x_5629_; 
v___x_5628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5628_, 0, v___y_5626_);
lean_ctor_set(v___x_5628_, 1, v_gs_5627_);
v___x_5629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5628_);
return v___x_5629_;
}
v___jp_5630_:
{
lean_object* v___x_5634_; 
v___x_5634_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5633_);
if (lean_obj_tag(v___x_5634_) == 0)
{
lean_object* v___x_5636_; uint8_t v_isShared_5637_; uint8_t v_isSharedCheck_5644_; 
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5634_);
if (v_isSharedCheck_5644_ == 0)
{
lean_object* v_unused_5645_; 
v_unused_5645_ = lean_ctor_get(v___x_5634_, 0);
lean_dec(v_unused_5645_);
v___x_5636_ = v___x_5634_;
v_isShared_5637_ = v_isSharedCheck_5644_;
goto v_resetjp_5635_;
}
else
{
lean_dec(v___x_5634_);
v___x_5636_ = lean_box(0);
v_isShared_5637_ = v_isSharedCheck_5644_;
goto v_resetjp_5635_;
}
v_resetjp_5635_:
{
lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5642_; 
v___x_5638_ = lean_box(0);
v___x_5639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5639_, 0, v_g_5632_);
lean_ctor_set(v___x_5639_, 1, v___x_5638_);
v___x_5640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5640_, 0, v___y_5631_);
lean_ctor_set(v___x_5640_, 1, v___x_5639_);
if (v_isShared_5637_ == 0)
{
lean_ctor_set(v___x_5636_, 0, v___x_5640_);
v___x_5642_ = v___x_5636_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v___x_5640_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
else
{
lean_object* v_a_5646_; lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
lean_dec(v_g_5632_);
lean_dec_ref(v___y_5631_);
v_a_5646_ = lean_ctor_get(v___x_5634_, 0);
v_isSharedCheck_5653_ = !lean_is_exclusive(v___x_5634_);
if (v_isSharedCheck_5653_ == 0)
{
v___x_5648_ = v___x_5634_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_inc(v_a_5646_);
lean_dec(v___x_5634_);
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
v___jp_5654_:
{
lean_object* v___x_5669_; 
v___x_5669_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5660_);
if (lean_obj_tag(v___x_5669_) == 0)
{
lean_object* v___x_5670_; 
lean_dec_ref_known(v___x_5669_, 1);
v___x_5670_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(v___y_5665_, v_goal_5588_, v___y_5655_, v___y_5664_, v___y_5668_, v___y_5660_, v___y_5663_, v___y_5666_, v___y_5657_, v___y_5656_, v___y_5658_, v___y_5661_, v___y_5667_, v___y_5659_, v___y_5662_);
return v___x_5670_;
}
else
{
lean_object* v_a_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5678_; 
lean_dec_ref(v___y_5665_);
lean_dec_ref(v___y_5664_);
lean_dec_ref(v___y_5655_);
lean_dec(v_goal_5588_);
v_a_5671_ = lean_ctor_get(v___x_5669_, 0);
v_isSharedCheck_5678_ = !lean_is_exclusive(v___x_5669_);
if (v_isSharedCheck_5678_ == 0)
{
v___x_5673_ = v___x_5669_;
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_a_5671_);
lean_dec(v___x_5669_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5678_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5676_; 
if (v_isShared_5674_ == 0)
{
v___x_5676_ = v___x_5673_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5677_; 
v_reuseFailAlloc_5677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5677_, 0, v_a_5671_);
v___x_5676_ = v_reuseFailAlloc_5677_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
return v___x_5676_;
}
}
}
}
v___jp_5679_:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; 
lean_dec_ref(v___y_5683_);
v___x_5695_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v___y_5681_);
lean_inc_ref(v___x_5695_);
v___x_5696_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v___x_5695_, v___y_5684_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
if (lean_obj_tag(v___x_5696_) == 0)
{
lean_object* v_a_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5798_; 
v_a_5697_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5699_ = v___x_5696_;
v_isShared_5700_ = v_isSharedCheck_5798_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_a_5697_);
lean_dec(v___x_5696_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5798_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
uint8_t v___x_5701_; 
v___x_5701_ = lean_unbox(v_a_5697_);
lean_dec(v_a_5697_);
if (v___x_5701_ == 0)
{
lean_object* v___x_5702_; 
lean_del_object(v___x_5699_);
lean_inc_ref(v___y_5681_);
lean_inc(v_goal_5588_);
v___x_5702_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_5588_, v___y_5681_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
if (lean_obj_tag(v___x_5702_) == 0)
{
lean_object* v_a_5703_; 
v_a_5703_ = lean_ctor_get(v___x_5702_, 0);
lean_inc(v_a_5703_);
lean_dec_ref_known(v___x_5702_, 1);
if (lean_obj_tag(v_a_5703_) == 1)
{
lean_object* v_val_5704_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_val_5704_ = lean_ctor_get(v_a_5703_, 0);
lean_inc(v_val_5704_);
lean_dec_ref_known(v_a_5703_, 1);
v___y_5619_ = v___y_5682_;
v_g_5620_ = v_val_5704_;
goto v___jp_5618_;
}
else
{
lean_object* v___x_5705_; 
lean_dec(v_a_5703_);
lean_inc_ref(v___y_5681_);
lean_inc(v_goal_5588_);
v___x_5705_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_5588_, v___y_5681_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
if (lean_obj_tag(v___x_5705_) == 0)
{
lean_object* v_a_5706_; 
v_a_5706_ = lean_ctor_get(v___x_5705_, 0);
lean_inc(v_a_5706_);
lean_dec_ref_known(v___x_5705_, 1);
if (lean_obj_tag(v_a_5706_) == 1)
{
lean_object* v_val_5707_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_val_5707_ = lean_ctor_get(v_a_5706_, 0);
lean_inc(v_val_5707_);
lean_dec_ref_known(v_a_5706_, 1);
v___y_5631_ = v___y_5682_;
v_g_5632_ = v_val_5707_;
v___y_5633_ = v___y_5685_;
goto v___jp_5630_;
}
else
{
lean_object* v___x_5708_; 
lean_dec(v_a_5706_);
lean_inc_ref(v___y_5681_);
lean_inc(v_goal_5588_);
v___x_5708_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_5588_, v___y_5681_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
if (lean_obj_tag(v___x_5708_) == 0)
{
lean_object* v_a_5709_; 
v_a_5709_ = lean_ctor_get(v___x_5708_, 0);
lean_inc(v_a_5709_);
lean_dec_ref_known(v___x_5708_, 1);
if (lean_obj_tag(v_a_5709_) == 1)
{
lean_object* v_val_5710_; lean_object* v___x_5711_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_val_5710_ = lean_ctor_get(v_a_5709_, 0);
lean_inc(v_val_5710_);
lean_dec_ref_known(v_a_5709_, 1);
v___x_5711_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5685_);
if (lean_obj_tag(v___x_5711_) == 0)
{
lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5719_; 
v_isSharedCheck_5719_ = !lean_is_exclusive(v___x_5711_);
if (v_isSharedCheck_5719_ == 0)
{
lean_object* v_unused_5720_; 
v_unused_5720_ = lean_ctor_get(v___x_5711_, 0);
lean_dec(v_unused_5720_);
v___x_5713_ = v___x_5711_;
v_isShared_5714_ = v_isSharedCheck_5719_;
goto v_resetjp_5712_;
}
else
{
lean_dec(v___x_5711_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5719_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5715_; lean_object* v___x_5717_; 
v___x_5715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5715_, 0, v___y_5682_);
lean_ctor_set(v___x_5715_, 1, v_val_5710_);
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 0, v___x_5715_);
v___x_5717_ = v___x_5713_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5715_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
else
{
lean_object* v_a_5721_; lean_object* v___x_5723_; uint8_t v_isShared_5724_; uint8_t v_isSharedCheck_5728_; 
lean_dec(v_val_5710_);
lean_dec_ref(v___y_5682_);
v_a_5721_ = lean_ctor_get(v___x_5711_, 0);
v_isSharedCheck_5728_ = !lean_is_exclusive(v___x_5711_);
if (v_isSharedCheck_5728_ == 0)
{
v___x_5723_ = v___x_5711_;
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
else
{
lean_inc(v_a_5721_);
lean_dec(v___x_5711_);
v___x_5723_ = lean_box(0);
v_isShared_5724_ = v_isSharedCheck_5728_;
goto v_resetjp_5722_;
}
v_resetjp_5722_:
{
lean_object* v___x_5726_; 
if (v_isShared_5724_ == 0)
{
v___x_5726_ = v___x_5723_;
goto v_reusejp_5725_;
}
else
{
lean_object* v_reuseFailAlloc_5727_; 
v_reuseFailAlloc_5727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5721_);
v___x_5726_ = v_reuseFailAlloc_5727_;
goto v_reusejp_5725_;
}
v_reusejp_5725_:
{
return v___x_5726_;
}
}
}
}
else
{
lean_object* v___x_5729_; 
lean_dec(v_a_5709_);
lean_inc_ref(v___y_5681_);
lean_inc(v_goal_5588_);
v___x_5729_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_5588_, v___y_5681_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_a_5730_);
lean_dec_ref_known(v___x_5729_, 1);
if (lean_obj_tag(v_a_5730_) == 1)
{
lean_object* v_val_5731_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_val_5731_ = lean_ctor_get(v_a_5730_, 0);
lean_inc(v_val_5731_);
lean_dec_ref_known(v_a_5730_, 1);
v___y_5631_ = v___y_5682_;
v_g_5632_ = v_val_5731_;
v___y_5633_ = v___y_5685_;
goto v___jp_5630_;
}
else
{
lean_object* v___x_5732_; 
lean_dec(v_a_5730_);
lean_inc_ref(v___y_5681_);
lean_inc(v_goal_5588_);
v___x_5732_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_5588_, v___y_5681_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
if (lean_obj_tag(v___x_5732_) == 0)
{
lean_object* v_a_5733_; 
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc(v_a_5733_);
lean_dec_ref_known(v___x_5732_, 1);
if (lean_obj_tag(v_a_5733_) == 1)
{
lean_object* v_val_5734_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_val_5734_ = lean_ctor_get(v_a_5733_, 0);
lean_inc(v_val_5734_);
lean_dec_ref_known(v_a_5733_, 1);
v___y_5631_ = v___y_5682_;
v_g_5632_ = v_val_5734_;
v___y_5633_ = v___y_5685_;
goto v___jp_5630_;
}
else
{
lean_object* v___x_5735_; uint8_t v___x_5736_; 
lean_dec(v_a_5733_);
v___x_5735_ = l_Lean_Expr_getAppFn(v___x_5695_);
v___x_5736_ = l_Lean_Expr_isConst(v___x_5735_);
if (v___x_5736_ == 0)
{
uint8_t v___x_5737_; 
v___x_5737_ = l_Lean_Expr_isFVar(v___x_5735_);
lean_dec_ref(v___x_5735_);
if (v___x_5737_ == 0)
{
lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v_a_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5751_; 
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v___x_5738_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v___x_5739_ = l_Lean_MessageData_ofExpr(v___x_5695_);
v___x_5740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5738_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3);
v___x_5742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5742_, 0, v___x_5740_);
lean_ctor_set(v___x_5742_, 1, v___x_5741_);
v___x_5743_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5742_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_);
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5751_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5751_ == 0)
{
v___x_5746_ = v___x_5743_;
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_a_5744_);
lean_dec(v___x_5743_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5751_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v___x_5749_; 
if (v_isShared_5747_ == 0)
{
v___x_5749_ = v___x_5746_;
goto v_reusejp_5748_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5744_);
v___x_5749_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5748_;
}
v_reusejp_5748_:
{
return v___x_5749_;
}
}
}
else
{
lean_dec_ref(v___x_5695_);
v___y_5655_ = v___y_5680_;
v___y_5656_ = v___y_5689_;
v___y_5657_ = v___y_5688_;
v___y_5658_ = v___y_5690_;
v___y_5659_ = v___y_5693_;
v___y_5660_ = v___y_5685_;
v___y_5661_ = v___y_5691_;
v___y_5662_ = v___y_5694_;
v___y_5663_ = v___y_5686_;
v___y_5664_ = v___y_5681_;
v___y_5665_ = v___y_5682_;
v___y_5666_ = v___y_5687_;
v___y_5667_ = v___y_5692_;
v___y_5668_ = v___y_5684_;
goto v___jp_5654_;
}
}
else
{
lean_dec_ref(v___x_5735_);
lean_dec_ref(v___x_5695_);
v___y_5655_ = v___y_5680_;
v___y_5656_ = v___y_5689_;
v___y_5657_ = v___y_5688_;
v___y_5658_ = v___y_5690_;
v___y_5659_ = v___y_5693_;
v___y_5660_ = v___y_5685_;
v___y_5661_ = v___y_5691_;
v___y_5662_ = v___y_5694_;
v___y_5663_ = v___y_5686_;
v___y_5664_ = v___y_5681_;
v___y_5665_ = v___y_5682_;
v___y_5666_ = v___y_5687_;
v___y_5667_ = v___y_5692_;
v___y_5668_ = v___y_5684_;
goto v___jp_5654_;
}
}
}
else
{
lean_object* v_a_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5759_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_a_5752_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5759_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5759_ == 0)
{
v___x_5754_ = v___x_5732_;
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_a_5752_);
lean_dec(v___x_5732_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5759_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
lean_object* v___x_5757_; 
if (v_isShared_5755_ == 0)
{
v___x_5757_ = v___x_5754_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5758_; 
v_reuseFailAlloc_5758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5758_, 0, v_a_5752_);
v___x_5757_ = v_reuseFailAlloc_5758_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
return v___x_5757_;
}
}
}
}
}
else
{
lean_object* v_a_5760_; lean_object* v___x_5762_; uint8_t v_isShared_5763_; uint8_t v_isSharedCheck_5767_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_a_5760_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5767_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5767_ == 0)
{
v___x_5762_ = v___x_5729_;
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
else
{
lean_inc(v_a_5760_);
lean_dec(v___x_5729_);
v___x_5762_ = lean_box(0);
v_isShared_5763_ = v_isSharedCheck_5767_;
goto v_resetjp_5761_;
}
v_resetjp_5761_:
{
lean_object* v___x_5765_; 
if (v_isShared_5763_ == 0)
{
v___x_5765_ = v___x_5762_;
goto v_reusejp_5764_;
}
else
{
lean_object* v_reuseFailAlloc_5766_; 
v_reuseFailAlloc_5766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5766_, 0, v_a_5760_);
v___x_5765_ = v_reuseFailAlloc_5766_;
goto v_reusejp_5764_;
}
v_reusejp_5764_:
{
return v___x_5765_;
}
}
}
}
}
else
{
lean_object* v_a_5768_; lean_object* v___x_5770_; uint8_t v_isShared_5771_; uint8_t v_isSharedCheck_5775_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_a_5768_ = lean_ctor_get(v___x_5708_, 0);
v_isSharedCheck_5775_ = !lean_is_exclusive(v___x_5708_);
if (v_isSharedCheck_5775_ == 0)
{
v___x_5770_ = v___x_5708_;
v_isShared_5771_ = v_isSharedCheck_5775_;
goto v_resetjp_5769_;
}
else
{
lean_inc(v_a_5768_);
lean_dec(v___x_5708_);
v___x_5770_ = lean_box(0);
v_isShared_5771_ = v_isSharedCheck_5775_;
goto v_resetjp_5769_;
}
v_resetjp_5769_:
{
lean_object* v___x_5773_; 
if (v_isShared_5771_ == 0)
{
v___x_5773_ = v___x_5770_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5774_; 
v_reuseFailAlloc_5774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_a_5768_);
v___x_5773_ = v_reuseFailAlloc_5774_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
return v___x_5773_;
}
}
}
}
}
else
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5783_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_a_5776_ = lean_ctor_get(v___x_5705_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v___x_5705_);
if (v_isSharedCheck_5783_ == 0)
{
v___x_5778_ = v___x_5705_;
v_isShared_5779_ = v_isSharedCheck_5783_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v___x_5705_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5783_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5781_; 
if (v_isShared_5779_ == 0)
{
v___x_5781_ = v___x_5778_;
goto v_reusejp_5780_;
}
else
{
lean_object* v_reuseFailAlloc_5782_; 
v_reuseFailAlloc_5782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_a_5776_);
v___x_5781_ = v_reuseFailAlloc_5782_;
goto v_reusejp_5780_;
}
v_reusejp_5780_:
{
return v___x_5781_;
}
}
}
}
}
else
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5791_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_a_5784_ = lean_ctor_get(v___x_5702_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5702_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5786_ = v___x_5702_;
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5702_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5787_ == 0)
{
v___x_5789_ = v___x_5786_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
}
else
{
lean_object* v___x_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5796_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v___x_5792_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v___y_5681_);
lean_dec_ref(v___y_5681_);
v___x_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5793_, 0, v___x_5792_);
v___x_5794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5794_, 0, v___x_5793_);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 0, v___x_5794_);
v___x_5796_ = v___x_5699_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v___x_5794_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
}
else
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5806_; 
lean_dec_ref(v___x_5695_);
lean_dec_ref(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v_goal_5588_);
v_a_5799_ = lean_ctor_get(v___x_5696_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5696_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5801_ = v___x_5696_;
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5696_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5804_; 
if (v_isShared_5802_ == 0)
{
v___x_5804_ = v___x_5801_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_a_5799_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_6068_, lean_object* v_scope_6069_, lean_object* v___y_6070_, lean_object* v___y_6071_, lean_object* v___y_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_, lean_object* v___y_6080_, lean_object* v___y_6081_){
_start:
{
lean_object* v_res_6082_; 
v_res_6082_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_6068_, v_scope_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
lean_dec(v___y_6080_);
lean_dec_ref(v___y_6079_);
lean_dec(v___y_6078_);
lean_dec_ref(v___y_6077_);
lean_dec(v___y_6076_);
lean_dec_ref(v___y_6075_);
lean_dec(v___y_6074_);
lean_dec_ref(v___y_6073_);
lean_dec(v___y_6072_);
lean_dec(v___y_6071_);
lean_dec_ref(v___y_6070_);
return v_res_6082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_scope_6083_, lean_object* v_goal_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_, lean_object* v_a_6091_, lean_object* v_a_6092_, lean_object* v_a_6093_, lean_object* v_a_6094_, lean_object* v_a_6095_){
_start:
{
lean_object* v___f_6097_; lean_object* v___x_6098_; 
lean_inc(v_goal_6084_);
v___f_6097_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6097_, 0, v_goal_6084_);
lean_closure_set(v___f_6097_, 1, v_scope_6083_);
v___x_6098_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6084_, v___f_6097_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_, v_a_6092_, v_a_6093_, v_a_6094_, v_a_6095_);
return v___x_6098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_scope_6099_, lean_object* v_goal_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_, lean_object* v_a_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_){
_start:
{
lean_object* v_res_6113_; 
v_res_6113_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_6099_, v_goal_6100_, v_a_6101_, v_a_6102_, v_a_6103_, v_a_6104_, v_a_6105_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_, v_a_6111_);
lean_dec(v_a_6111_);
lean_dec_ref(v_a_6110_);
lean_dec(v_a_6109_);
lean_dec_ref(v_a_6108_);
lean_dec(v_a_6107_);
lean_dec_ref(v_a_6106_);
lean_dec(v_a_6105_);
lean_dec_ref(v_a_6104_);
lean_dec(v_a_6103_);
lean_dec(v_a_6102_);
lean_dec_ref(v_a_6101_);
return v_res_6113_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Solve(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
