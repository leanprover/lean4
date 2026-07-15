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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateMVarsS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4;
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0;
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2;
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
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4(void){
_start:
{
uint8_t v___x_2837_; uint64_t v___x_2838_; 
v___x_2837_ = 2;
v___x_2838_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object* v_goal_2839_, lean_object* v_info_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_2840_);
lean_inc_ref(v___x_2853_);
v___x_2854_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_2853_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_3028_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_3028_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_3028_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
if (lean_obj_tag(v_a_2855_) == 1)
{
lean_object* v_val_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_3023_; 
lean_del_object(v___x_2857_);
v_val_2859_ = lean_ctor_get(v_a_2855_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_a_2855_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_2861_ = v_a_2855_;
v_isShared_2862_ = v_isSharedCheck_3023_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_val_2859_);
lean_dec(v_a_2855_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_3023_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___y_2864_; lean_object* v___y_2865_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2868_; lean_object* v___y_2869_; lean_object* v___y_2870_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___y_2873_; lean_object* v___y_2874_; 
if (lean_obj_tag(v_val_2859_) == 2)
{
lean_object* v___x_2931_; uint8_t v_foApprox_2932_; uint8_t v_ctxApprox_2933_; uint8_t v_quasiPatternApprox_2934_; uint8_t v_constApprox_2935_; uint8_t v_isDefEqStuckEx_2936_; uint8_t v_unificationHints_2937_; uint8_t v_proofIrrelevance_2938_; uint8_t v_assignSyntheticOpaque_2939_; uint8_t v_offsetCnstrs_2940_; uint8_t v_etaStruct_2941_; uint8_t v_univApprox_2942_; uint8_t v_iota_2943_; uint8_t v_beta_2944_; uint8_t v_proj_2945_; uint8_t v_zeta_2946_; uint8_t v_zetaDelta_2947_; uint8_t v_zetaUnused_2948_; uint8_t v_zetaHave_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_3022_; 
v___x_2931_ = l_Lean_Meta_Context_config(v_a_2848_);
v_foApprox_2932_ = lean_ctor_get_uint8(v___x_2931_, 0);
v_ctxApprox_2933_ = lean_ctor_get_uint8(v___x_2931_, 1);
v_quasiPatternApprox_2934_ = lean_ctor_get_uint8(v___x_2931_, 2);
v_constApprox_2935_ = lean_ctor_get_uint8(v___x_2931_, 3);
v_isDefEqStuckEx_2936_ = lean_ctor_get_uint8(v___x_2931_, 4);
v_unificationHints_2937_ = lean_ctor_get_uint8(v___x_2931_, 5);
v_proofIrrelevance_2938_ = lean_ctor_get_uint8(v___x_2931_, 6);
v_assignSyntheticOpaque_2939_ = lean_ctor_get_uint8(v___x_2931_, 7);
v_offsetCnstrs_2940_ = lean_ctor_get_uint8(v___x_2931_, 8);
v_etaStruct_2941_ = lean_ctor_get_uint8(v___x_2931_, 10);
v_univApprox_2942_ = lean_ctor_get_uint8(v___x_2931_, 11);
v_iota_2943_ = lean_ctor_get_uint8(v___x_2931_, 12);
v_beta_2944_ = lean_ctor_get_uint8(v___x_2931_, 13);
v_proj_2945_ = lean_ctor_get_uint8(v___x_2931_, 14);
v_zeta_2946_ = lean_ctor_get_uint8(v___x_2931_, 15);
v_zetaDelta_2947_ = lean_ctor_get_uint8(v___x_2931_, 16);
v_zetaUnused_2948_ = lean_ctor_get_uint8(v___x_2931_, 17);
v_zetaHave_2949_ = lean_ctor_get_uint8(v___x_2931_, 18);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_2951_ = v___x_2931_;
v_isShared_2952_ = v_isSharedCheck_3022_;
goto v_resetjp_2950_;
}
else
{
lean_dec(v___x_2931_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_3022_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
uint8_t v_trackZetaDelta_2953_; lean_object* v_zetaDeltaSet_2954_; lean_object* v_lctx_2955_; lean_object* v_localInstances_2956_; lean_object* v_defEqCtx_x3f_2957_; lean_object* v_synthPendingDepth_2958_; lean_object* v_canUnfold_x3f_2959_; uint8_t v_univApprox_2960_; uint8_t v_inTypeClassResolution_2961_; uint8_t v_cacheInferType_2962_; uint8_t v___x_2963_; lean_object* v_config_2965_; 
v_trackZetaDelta_2953_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*7);
v_zetaDeltaSet_2954_ = lean_ctor_get(v_a_2848_, 1);
v_lctx_2955_ = lean_ctor_get(v_a_2848_, 2);
v_localInstances_2956_ = lean_ctor_get(v_a_2848_, 3);
v_defEqCtx_x3f_2957_ = lean_ctor_get(v_a_2848_, 4);
v_synthPendingDepth_2958_ = lean_ctor_get(v_a_2848_, 5);
v_canUnfold_x3f_2959_ = lean_ctor_get(v_a_2848_, 6);
v_univApprox_2960_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2961_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*7 + 2);
v_cacheInferType_2962_ = lean_ctor_get_uint8(v_a_2848_, sizeof(void*)*7 + 3);
v___x_2963_ = 2;
if (v_isShared_2952_ == 0)
{
v_config_2965_ = v___x_2951_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 0, v_foApprox_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 1, v_ctxApprox_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 2, v_quasiPatternApprox_2934_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 3, v_constApprox_2935_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 4, v_isDefEqStuckEx_2936_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 5, v_unificationHints_2937_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 6, v_proofIrrelevance_2938_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 7, v_assignSyntheticOpaque_2939_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 8, v_offsetCnstrs_2940_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 10, v_etaStruct_2941_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 11, v_univApprox_2942_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 12, v_iota_2943_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 13, v_beta_2944_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 14, v_proj_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 15, v_zeta_2946_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 16, v_zetaDelta_2947_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 17, v_zetaUnused_2948_);
lean_ctor_set_uint8(v_reuseFailAlloc_3021_, 18, v_zetaHave_2949_);
v_config_2965_ = v_reuseFailAlloc_3021_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
uint64_t v___x_2966_; uint64_t v___x_2967_; uint64_t v___x_2968_; uint64_t v___x_2969_; uint64_t v___x_2970_; uint64_t v_key_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_ctor_set_uint8(v_config_2965_, 9, v___x_2963_);
v___x_2966_ = l_Lean_Meta_Context_configKey(v_a_2848_);
v___x_2967_ = 3ULL;
v___x_2968_ = lean_uint64_shift_right(v___x_2966_, v___x_2967_);
v___x_2969_ = lean_uint64_shift_left(v___x_2968_, v___x_2967_);
v___x_2970_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4);
v_key_2971_ = lean_uint64_lor(v___x_2969_, v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2972_, 0, v_config_2965_);
lean_ctor_set_uint64(v___x_2972_, sizeof(void*)*1, v_key_2971_);
lean_inc(v_canUnfold_x3f_2959_);
lean_inc(v_synthPendingDepth_2958_);
lean_inc(v_defEqCtx_x3f_2957_);
lean_inc_ref(v_localInstances_2956_);
lean_inc_ref(v_lctx_2955_);
lean_inc(v_zetaDeltaSet_2954_);
v___x_2973_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_zetaDeltaSet_2954_);
lean_ctor_set(v___x_2973_, 2, v_lctx_2955_);
lean_ctor_set(v___x_2973_, 3, v_localInstances_2956_);
lean_ctor_set(v___x_2973_, 4, v_defEqCtx_x3f_2957_);
lean_ctor_set(v___x_2973_, 5, v_synthPendingDepth_2958_);
lean_ctor_set(v___x_2973_, 6, v_canUnfold_x3f_2959_);
lean_ctor_set_uint8(v___x_2973_, sizeof(void*)*7, v_trackZetaDelta_2953_);
lean_ctor_set_uint8(v___x_2973_, sizeof(void*)*7 + 1, v_univApprox_2960_);
lean_ctor_set_uint8(v___x_2973_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2961_);
lean_ctor_set_uint8(v___x_2973_, sizeof(void*)*7 + 3, v_cacheInferType_2962_);
v___x_2974_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_2853_, v___x_2973_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec_ref_known(v___x_2973_, 7);
if (lean_obj_tag(v___x_2974_) == 0)
{
lean_object* v_a_2975_; 
v_a_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_a_2975_);
lean_dec_ref_known(v___x_2974_, 1);
if (lean_obj_tag(v_a_2975_) == 1)
{
lean_object* v_val_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref_known(v_val_2859_, 1);
lean_del_object(v___x_2861_);
lean_dec_ref(v___x_2853_);
v_val_2976_ = lean_ctor_get(v_a_2975_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v_a_2975_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2978_ = v_a_2975_;
v_isShared_2979_ = v_isSharedCheck_3012_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_val_2976_);
lean_dec(v_a_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3012_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2976_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2839_, v_info_2840_, v_a_2981_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2995_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2995_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2995_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2990_; 
v___x_2987_ = lean_box(0);
v___x_2988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2988_, 0, v_a_2983_);
lean_ctor_set(v___x_2988_, 1, v___x_2987_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 0, v___x_2988_);
v___x_2990_ = v___x_2978_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v___x_2988_);
v___x_2990_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2992_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v___x_2990_);
v___x_2992_ = v___x_2985_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_del_object(v___x_2978_);
v_a_2996_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2982_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2982_);
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
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_del_object(v___x_2978_);
lean_dec_ref(v_info_2840_);
lean_dec(v_goal_2839_);
v_a_3004_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2980_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2980_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
else
{
lean_dec(v_a_2975_);
v___y_2864_ = v_a_2841_;
v___y_2865_ = v_a_2842_;
v___y_2866_ = v_a_2843_;
v___y_2867_ = v_a_2844_;
v___y_2868_ = v_a_2845_;
v___y_2869_ = v_a_2846_;
v___y_2870_ = v_a_2847_;
v___y_2871_ = v_a_2848_;
v___y_2872_ = v_a_2849_;
v___y_2873_ = v_a_2850_;
v___y_2874_ = v_a_2851_;
goto v___jp_2863_;
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref_known(v_val_2859_, 1);
lean_del_object(v___x_2861_);
lean_dec_ref(v___x_2853_);
lean_dec_ref(v_info_2840_);
lean_dec(v_goal_2839_);
v_a_3013_ = lean_ctor_get(v___x_2974_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2974_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2974_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
}
else
{
v___y_2864_ = v_a_2841_;
v___y_2865_ = v_a_2842_;
v___y_2866_ = v_a_2843_;
v___y_2867_ = v_a_2844_;
v___y_2868_ = v_a_2845_;
v___y_2869_ = v_a_2846_;
v___y_2870_ = v_a_2847_;
v___y_2871_ = v_a_2848_;
v___y_2872_ = v_a_2849_;
v___y_2873_ = v_a_2850_;
v___y_2874_ = v_a_2851_;
goto v___jp_2863_;
}
v___jp_2863_:
{
lean_object* v___x_2875_; 
v___x_2875_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_2859_, v_info_2840_, v___y_2865_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2875_) == 0)
{
lean_object* v_a_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v_a_2876_ = lean_ctor_get(v___x_2875_, 0);
lean_inc(v_a_2876_);
lean_dec_ref_known(v___x_2875_, 1);
v___x_2877_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1);
v___x_2878_ = l_Lean_indentExpr(v___x_2853_);
lean_inc_ref(v___x_2878_);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2879_);
v___x_2881_ = v___x_2861_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; 
v___x_2882_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2876_, v_goal_2839_, v___x_2881_, v___y_2864_, v___y_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
if (lean_obj_tag(v___x_2882_) == 0)
{
lean_object* v_a_2883_; 
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_a_2883_);
lean_dec_ref_known(v___x_2882_, 1);
if (lean_obj_tag(v_a_2883_) == 1)
{
lean_object* v_mvarIds_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2910_; 
lean_dec_ref(v___x_2878_);
v_mvarIds_2884_ = lean_ctor_get(v_a_2883_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_a_2883_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2886_ = v_a_2883_;
v_isShared_2887_ = v_isSharedCheck_2910_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_mvarIds_2884_);
lean_dec(v_a_2883_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2910_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2889_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_2884_, v___x_2888_, v___y_2864_, v___y_2865_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
lean_dec(v_mvarIds_2884_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2901_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2892_ = v___x_2889_;
v_isShared_2893_ = v_isSharedCheck_2901_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2889_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2901_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2894_ = lean_array_to_list(v_a_2890_);
if (v_isShared_2887_ == 0)
{
lean_ctor_set(v___x_2886_, 0, v___x_2894_);
v___x_2896_ = v___x_2886_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v___x_2894_);
v___x_2896_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2893_ == 0)
{
lean_ctor_set(v___x_2892_, 0, v___x_2896_);
v___x_2898_ = v___x_2892_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_del_object(v___x_2886_);
v_a_2902_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2889_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2889_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
lean_dec(v_a_2883_);
v___x_2911_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v___x_2878_);
v___x_2913_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2912_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
return v___x_2913_;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___x_2878_);
v_a_2914_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2882_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2882_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_del_object(v___x_2861_);
lean_dec_ref(v___x_2853_);
lean_dec(v_goal_2839_);
v_a_2923_ = lean_ctor_get(v___x_2875_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2875_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2875_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2875_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
lean_dec(v_a_2855_);
lean_dec_ref(v___x_2853_);
lean_dec_ref(v_info_2840_);
lean_dec(v_goal_2839_);
v___x_3024_ = lean_box(0);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_3024_);
v___x_3026_ = v___x_2857_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec_ref(v___x_2853_);
lean_dec_ref(v_info_2840_);
lean_dec(v_goal_2839_);
v_a_3029_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2854_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2854_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3037_, lean_object* v_info_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_3037_, v_info_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec_ref(v_a_3046_);
lean_dec(v_a_3045_);
lean_dec_ref(v_a_3044_);
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec(v_a_3040_);
lean_dec_ref(v_a_3039_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3052_, lean_object* v_as_x27_3053_, lean_object* v_b_3054_, lean_object* v_a_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3053_, v_b_3054_, v___y_3056_, v___y_3057_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3069_, lean_object* v_as_x27_3070_, lean_object* v_b_3071_, lean_object* v_a_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(v_as_3069_, v_as_x27_3070_, v_b_3071_, v_a_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec_ref(v___y_3073_);
lean_dec(v_as_x27_3070_);
lean_dec(v_as_3069_);
return v_res_3085_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3088_ = l_Lean_stringToMessageData(v___x_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3089_, lean_object* v_info_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v___x_3103_; lean_object* v_f_3104_; lean_object* v___x_3105_; 
v___x_3103_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3090_);
v_f_3104_ = l_Lean_Expr_getAppFn(v___x_3103_);
v___x_3105_ = l_Lean_Expr_fvarId_x3f(v_f_3104_);
lean_dec_ref(v_f_3104_);
if (lean_obj_tag(v___x_3105_) == 1)
{
lean_object* v_val_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; 
v_val_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc_n(v_val_3106_, 2);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = 0;
v___x_3108_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3106_, v___x_3107_, v_a_3098_, v_a_3100_, v_a_3101_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3196_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3111_ = v___x_3108_;
v_isShared_3112_ = v_isSharedCheck_3196_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v___x_3108_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3196_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
if (lean_obj_tag(v_a_3109_) == 1)
{
lean_object* v_val_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3191_; 
lean_del_object(v___x_3111_);
v_val_3113_ = lean_ctor_get(v_a_3109_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_a_3109_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3115_ = v_a_3109_;
v_isShared_3116_ = v_isSharedCheck_3191_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_val_3113_);
lean_dec(v_a_3109_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3191_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v_options_3163_; uint8_t v_hasTrace_3164_; 
v_options_3163_ = lean_ctor_get(v_a_3100_, 2);
v_hasTrace_3164_ = lean_ctor_get_uint8(v_options_3163_, sizeof(void*)*1);
if (v_hasTrace_3164_ == 0)
{
lean_dec(v_val_3106_);
v___y_3118_ = v_a_3091_;
v___y_3119_ = v_a_3092_;
v___y_3120_ = v_a_3093_;
v___y_3121_ = v_a_3094_;
v___y_3122_ = v_a_3095_;
v___y_3123_ = v_a_3096_;
v___y_3124_ = v_a_3097_;
v___y_3125_ = v_a_3098_;
v___y_3126_ = v_a_3099_;
v___y_3127_ = v_a_3100_;
v___y_3128_ = v_a_3101_;
goto v___jp_3117_;
}
else
{
lean_object* v_inheritedTraceOptions_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_inheritedTraceOptions_3165_ = lean_ctor_get(v_a_3100_, 13);
v___x_3166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3167_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3165_, v_options_3163_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_dec(v_val_3106_);
v___y_3118_ = v_a_3091_;
v___y_3119_ = v_a_3092_;
v___y_3120_ = v_a_3093_;
v___y_3121_ = v_a_3094_;
v___y_3122_ = v_a_3095_;
v___y_3123_ = v_a_3096_;
v___y_3124_ = v_a_3097_;
v___y_3125_ = v_a_3098_;
v___y_3126_ = v_a_3099_;
v___y_3127_ = v_a_3100_;
v___y_3128_ = v_a_3101_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Lean_FVarId_getUserName___redArg(v_val_3106_, v_a_3098_, v_a_3100_, v_a_3101_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3171_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3172_ = l_Lean_MessageData_ofName(v_a_3170_);
v___x_3173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3171_);
lean_ctor_set(v___x_3173_, 1, v___x_3172_);
v___x_3174_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3166_, v___x_3173_, v_a_3098_, v_a_3099_, v_a_3100_, v_a_3101_);
if (lean_obj_tag(v___x_3174_) == 0)
{
lean_dec_ref_known(v___x_3174_, 1);
v___y_3118_ = v_a_3091_;
v___y_3119_ = v_a_3092_;
v___y_3120_ = v_a_3093_;
v___y_3121_ = v_a_3094_;
v___y_3122_ = v_a_3095_;
v___y_3123_ = v_a_3096_;
v___y_3124_ = v_a_3097_;
v___y_3125_ = v_a_3098_;
v___y_3126_ = v_a_3099_;
v___y_3127_ = v_a_3100_;
v___y_3128_ = v_a_3101_;
goto v___jp_3117_;
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_del_object(v___x_3115_);
lean_dec(v_val_3113_);
lean_dec_ref(v___x_3103_);
lean_dec_ref(v_info_3090_);
lean_dec(v_goal_3089_);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_object* v_a_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3190_; 
lean_del_object(v___x_3115_);
lean_dec(v_val_3113_);
lean_dec_ref(v___x_3103_);
lean_dec_ref(v_info_3090_);
lean_dec(v_goal_3089_);
v_a_3183_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3185_ = v___x_3169_;
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_a_3183_);
lean_dec(v___x_3169_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3190_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v___x_3188_; 
if (v_isShared_3186_ == 0)
{
v___x_3188_ = v___x_3185_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
v___x_3188_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
return v___x_3188_;
}
}
}
}
}
v___jp_3117_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3129_ = l_Lean_Expr_getAppNumArgs(v___x_3103_);
v___x_3130_ = lean_mk_empty_array_with_capacity(v___x_3129_);
lean_dec(v___x_3129_);
v___x_3131_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3103_, v___x_3130_);
v___x_3132_ = l_Lean_Expr_betaRev(v_val_3113_, v___x_3131_, v___x_3107_, v___x_3107_);
lean_dec_ref(v___x_3131_);
v___x_3133_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3132_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3135_; 
v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_a_3134_);
lean_dec_ref_known(v___x_3133_, 1);
v___x_3135_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3089_, v_info_3090_, v_a_3134_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3146_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3146_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3146_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_a_3136_);
v___x_3141_ = v___x_3115_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3141_);
v___x_3143_ = v___x_3138_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_del_object(v___x_3115_);
v_a_3147_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3135_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3135_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_del_object(v___x_3115_);
lean_dec_ref(v_info_3090_);
lean_dec(v_goal_3089_);
v_a_3155_ = lean_ctor_get(v___x_3133_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3133_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3133_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_dec(v_a_3109_);
lean_dec(v_val_3106_);
lean_dec_ref(v___x_3103_);
lean_dec_ref(v_info_3090_);
lean_dec(v_goal_3089_);
v___x_3192_ = lean_box(0);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 0, v___x_3192_);
v___x_3194_ = v___x_3111_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3192_);
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
lean_dec(v_val_3106_);
lean_dec_ref(v___x_3103_);
lean_dec_ref(v_info_3090_);
lean_dec(v_goal_3089_);
v_a_3197_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3204_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3199_ = v___x_3108_;
v_isShared_3200_ = v_isSharedCheck_3204_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___x_3108_);
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
lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec(v___x_3105_);
lean_dec_ref(v___x_3103_);
lean_dec_ref(v_info_3090_);
lean_dec(v_goal_3089_);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
return v___x_3206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3207_, lean_object* v_info_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_3207_, v_info_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_a_3217_);
lean_dec_ref(v_a_3216_);
lean_dec(v_a_3215_);
lean_dec_ref(v_a_3214_);
lean_dec(v_a_3213_);
lean_dec_ref(v_a_3212_);
lean_dec(v_a_3211_);
lean_dec(v_a_3210_);
lean_dec_ref(v_a_3209_);
return v_res_3221_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0(void){
_start:
{
uint8_t v___x_3222_; uint64_t v___x_3223_; 
v___x_3222_ = 3;
v___x_3223_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3222_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3224_, lean_object* v_info_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_){
_start:
{
lean_object* v___x_3238_; lean_object* v_a_3240_; lean_object* v_f_3301_; 
v___x_3238_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3225_);
v_f_3301_ = l_Lean_Expr_getAppFn(v___x_3238_);
if (lean_obj_tag(v_f_3301_) == 11)
{
lean_object* v___x_3302_; uint8_t v_foApprox_3303_; uint8_t v_ctxApprox_3304_; uint8_t v_quasiPatternApprox_3305_; uint8_t v_constApprox_3306_; uint8_t v_isDefEqStuckEx_3307_; uint8_t v_unificationHints_3308_; uint8_t v_proofIrrelevance_3309_; uint8_t v_assignSyntheticOpaque_3310_; uint8_t v_offsetCnstrs_3311_; uint8_t v_etaStruct_3312_; uint8_t v_univApprox_3313_; uint8_t v_iota_3314_; uint8_t v_beta_3315_; uint8_t v_proj_3316_; uint8_t v_zeta_3317_; uint8_t v_zetaDelta_3318_; uint8_t v_zetaUnused_3319_; uint8_t v_zetaHave_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3357_; 
v___x_3302_ = l_Lean_Meta_Context_config(v_a_3233_);
v_foApprox_3303_ = lean_ctor_get_uint8(v___x_3302_, 0);
v_ctxApprox_3304_ = lean_ctor_get_uint8(v___x_3302_, 1);
v_quasiPatternApprox_3305_ = lean_ctor_get_uint8(v___x_3302_, 2);
v_constApprox_3306_ = lean_ctor_get_uint8(v___x_3302_, 3);
v_isDefEqStuckEx_3307_ = lean_ctor_get_uint8(v___x_3302_, 4);
v_unificationHints_3308_ = lean_ctor_get_uint8(v___x_3302_, 5);
v_proofIrrelevance_3309_ = lean_ctor_get_uint8(v___x_3302_, 6);
v_assignSyntheticOpaque_3310_ = lean_ctor_get_uint8(v___x_3302_, 7);
v_offsetCnstrs_3311_ = lean_ctor_get_uint8(v___x_3302_, 8);
v_etaStruct_3312_ = lean_ctor_get_uint8(v___x_3302_, 10);
v_univApprox_3313_ = lean_ctor_get_uint8(v___x_3302_, 11);
v_iota_3314_ = lean_ctor_get_uint8(v___x_3302_, 12);
v_beta_3315_ = lean_ctor_get_uint8(v___x_3302_, 13);
v_proj_3316_ = lean_ctor_get_uint8(v___x_3302_, 14);
v_zeta_3317_ = lean_ctor_get_uint8(v___x_3302_, 15);
v_zetaDelta_3318_ = lean_ctor_get_uint8(v___x_3302_, 16);
v_zetaUnused_3319_ = lean_ctor_get_uint8(v___x_3302_, 17);
v_zetaHave_3320_ = lean_ctor_get_uint8(v___x_3302_, 18);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3302_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3322_ = v___x_3302_;
v_isShared_3323_ = v_isSharedCheck_3357_;
goto v_resetjp_3321_;
}
else
{
lean_dec(v___x_3302_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3357_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
uint8_t v_trackZetaDelta_3324_; lean_object* v_zetaDeltaSet_3325_; lean_object* v_lctx_3326_; lean_object* v_localInstances_3327_; lean_object* v_defEqCtx_x3f_3328_; lean_object* v_synthPendingDepth_3329_; lean_object* v_canUnfold_x3f_3330_; uint8_t v_univApprox_3331_; uint8_t v_inTypeClassResolution_3332_; uint8_t v_cacheInferType_3333_; uint8_t v___x_3334_; lean_object* v_config_3336_; 
v_trackZetaDelta_3324_ = lean_ctor_get_uint8(v_a_3233_, sizeof(void*)*7);
v_zetaDeltaSet_3325_ = lean_ctor_get(v_a_3233_, 1);
v_lctx_3326_ = lean_ctor_get(v_a_3233_, 2);
v_localInstances_3327_ = lean_ctor_get(v_a_3233_, 3);
v_defEqCtx_x3f_3328_ = lean_ctor_get(v_a_3233_, 4);
v_synthPendingDepth_3329_ = lean_ctor_get(v_a_3233_, 5);
v_canUnfold_x3f_3330_ = lean_ctor_get(v_a_3233_, 6);
v_univApprox_3331_ = lean_ctor_get_uint8(v_a_3233_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3332_ = lean_ctor_get_uint8(v_a_3233_, sizeof(void*)*7 + 2);
v_cacheInferType_3333_ = lean_ctor_get_uint8(v_a_3233_, sizeof(void*)*7 + 3);
v___x_3334_ = 3;
if (v_isShared_3323_ == 0)
{
v_config_3336_ = v___x_3322_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 0, v_foApprox_3303_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 1, v_ctxApprox_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 2, v_quasiPatternApprox_3305_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 3, v_constApprox_3306_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 4, v_isDefEqStuckEx_3307_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 5, v_unificationHints_3308_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 6, v_proofIrrelevance_3309_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 7, v_assignSyntheticOpaque_3310_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 8, v_offsetCnstrs_3311_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 10, v_etaStruct_3312_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 11, v_univApprox_3313_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 12, v_iota_3314_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 13, v_beta_3315_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 14, v_proj_3316_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 15, v_zeta_3317_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 16, v_zetaDelta_3318_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 17, v_zetaUnused_3319_);
lean_ctor_set_uint8(v_reuseFailAlloc_3356_, 18, v_zetaHave_3320_);
v_config_3336_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
uint64_t v___x_3337_; uint64_t v___x_3338_; uint64_t v___x_3339_; uint64_t v___x_3340_; uint64_t v___x_3341_; uint64_t v_key_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
lean_ctor_set_uint8(v_config_3336_, 9, v___x_3334_);
v___x_3337_ = l_Lean_Meta_Context_configKey(v_a_3233_);
v___x_3338_ = 3ULL;
v___x_3339_ = lean_uint64_shift_right(v___x_3337_, v___x_3338_);
v___x_3340_ = lean_uint64_shift_left(v___x_3339_, v___x_3338_);
v___x_3341_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0);
v_key_3342_ = lean_uint64_lor(v___x_3340_, v___x_3341_);
v___x_3343_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3343_, 0, v_config_3336_);
lean_ctor_set_uint64(v___x_3343_, sizeof(void*)*1, v_key_3342_);
lean_inc(v_canUnfold_x3f_3330_);
lean_inc(v_synthPendingDepth_3329_);
lean_inc(v_defEqCtx_x3f_3328_);
lean_inc_ref(v_localInstances_3327_);
lean_inc_ref(v_lctx_3326_);
lean_inc(v_zetaDeltaSet_3325_);
v___x_3344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v_zetaDeltaSet_3325_);
lean_ctor_set(v___x_3344_, 2, v_lctx_3326_);
lean_ctor_set(v___x_3344_, 3, v_localInstances_3327_);
lean_ctor_set(v___x_3344_, 4, v_defEqCtx_x3f_3328_);
lean_ctor_set(v___x_3344_, 5, v_synthPendingDepth_3329_);
lean_ctor_set(v___x_3344_, 6, v_canUnfold_x3f_3330_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7, v_trackZetaDelta_3324_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 1, v_univApprox_3331_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3332_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 3, v_cacheInferType_3333_);
v___x_3345_ = l_Lean_Meta_reduceProj_x3f(v_f_3301_, v___x_3344_, v_a_3234_, v_a_3235_, v_a_3236_);
lean_dec_ref_known(v___x_3344_, 7);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v_a_3240_ = v_a_3346_;
goto v___jp_3239_;
}
else
{
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3347_; 
v_a_3347_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3347_);
lean_dec_ref_known(v___x_3345_, 1);
v_a_3240_ = v_a_3347_;
goto v___jp_3239_;
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_info_3225_);
lean_dec(v_goal_3224_);
v_a_3348_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3345_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3345_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_dec_ref(v_f_3301_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_info_3225_);
lean_dec(v_goal_3224_);
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
v___jp_3239_:
{
if (lean_obj_tag(v_a_3240_) == 1)
{
lean_object* v_val_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3298_; 
v_val_3241_ = lean_ctor_get(v_a_3240_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v_a_3240_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3243_ = v_a_3240_;
v_isShared_3244_ = v_isSharedCheck_3298_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_val_3241_);
lean_dec(v_a_3240_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3298_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3245_; 
v___x_3245_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3241_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v_a_3246_; lean_object* v___x_3247_; 
v_a_3246_ = lean_ctor_get(v___x_3245_, 0);
lean_inc(v_a_3246_);
lean_dec_ref_known(v___x_3245_, 1);
v___x_3247_ = l_Lean_Meta_Sym_shareCommon(v_a_3246_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3249_ = l_Lean_Expr_getAppNumArgs(v___x_3238_);
v___x_3250_ = lean_mk_empty_array_with_capacity(v___x_3249_);
lean_dec(v___x_3249_);
v___x_3251_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3238_, v___x_3250_);
v___x_3252_ = l_Lean_Meta_Sym_betaRevS(v_a_3248_, v___x_3251_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v___x_3254_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3224_, v_info_3225_, v_a_3253_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3265_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3265_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3265_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3244_ == 0)
{
lean_ctor_set(v___x_3243_, 0, v_a_3255_);
v___x_3260_ = v___x_3243_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3262_; 
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3260_);
v___x_3262_ = v___x_3257_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3260_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_del_object(v___x_3243_);
v_a_3266_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3254_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3254_);
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
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_del_object(v___x_3243_);
lean_dec_ref(v_info_3225_);
lean_dec(v_goal_3224_);
v_a_3274_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3252_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3252_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_del_object(v___x_3243_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_info_3225_);
lean_dec(v_goal_3224_);
v_a_3282_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3247_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3247_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_del_object(v___x_3243_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_info_3225_);
lean_dec(v_goal_3224_);
v_a_3290_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3245_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3245_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
}
else
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_dec(v_a_3240_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v_info_3225_);
lean_dec(v_goal_3224_);
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
return v___x_3300_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_3360_, lean_object* v_info_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_3360_, v_info_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_a_3368_);
lean_dec_ref(v_a_3367_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
return v_res_3374_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; 
v___x_3376_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_3377_ = l_Lean_stringToMessageData(v___x_3376_);
return v___x_3377_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3379_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_3380_ = l_Lean_stringToMessageData(v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_3383_ = l_Lean_stringToMessageData(v___x_3382_);
return v___x_3383_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_3386_ = l_Lean_stringToMessageData(v___x_3385_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_3387_, lean_object* v_a_3388_){
_start:
{
if (lean_obj_tag(v_a_3387_) == 0)
{
lean_object* v___x_3389_; 
v___x_3389_ = l_List_reverse___redArg(v_a_3388_);
return v___x_3389_;
}
else
{
lean_object* v_head_3390_; lean_object* v_tail_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3419_; 
v_head_3390_ = lean_ctor_get(v_a_3387_, 0);
v_tail_3391_ = lean_ctor_get(v_a_3387_, 1);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_a_3387_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3393_ = v_a_3387_;
v_isShared_3394_ = v_isSharedCheck_3419_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_tail_3391_);
lean_inc(v_head_3390_);
lean_dec(v_a_3387_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3419_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___y_3396_; 
switch(lean_obj_tag(v_head_3390_))
{
case 0:
{
lean_object* v_declName_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_declName_3401_ = lean_ctor_get(v_head_3390_, 0);
lean_inc(v_declName_3401_);
lean_dec_ref_known(v_head_3390_, 1);
v___x_3402_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3403_ = l_Lean_MessageData_ofName(v_declName_3401_);
v___x_3404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3402_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
v___y_3396_ = v___x_3404_;
goto v___jp_3395_;
}
case 1:
{
lean_object* v_fvarId_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_fvarId_3405_ = lean_ctor_get(v_head_3390_, 0);
lean_inc(v_fvarId_3405_);
lean_dec_ref_known(v_head_3390_, 1);
v___x_3406_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3407_ = l_Lean_mkFVar(v_fvarId_3405_);
v___x_3408_ = l_Lean_MessageData_ofExpr(v___x_3407_);
v___x_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3406_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___y_3396_ = v___x_3409_;
goto v___jp_3395_;
}
default: 
{
lean_object* v_ref_3410_; lean_object* v_proof_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v_ref_3410_ = lean_ctor_get(v_head_3390_, 1);
lean_inc(v_ref_3410_);
v_proof_3411_ = lean_ctor_get(v_head_3390_, 2);
lean_inc_ref(v_proof_3411_);
lean_dec_ref_known(v_head_3390_, 3);
v___x_3412_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3413_ = l_Lean_MessageData_ofSyntax(v_ref_3410_);
v___x_3414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = l_Lean_MessageData_ofExpr(v_proof_3411_);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___y_3396_ = v___x_3418_;
goto v___jp_3395_;
}
}
v___jp_3395_:
{
lean_object* v___x_3398_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 1, v_a_3388_);
lean_ctor_set(v___x_3393_, 0, v___y_3396_);
v___x_3398_ = v___x_3393_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v___y_3396_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v_a_3388_);
v___x_3398_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
v_a_3387_ = v_tail_3391_;
v_a_3388_ = v___x_3398_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_3420_, size_t v_i_3421_, lean_object* v_bs_3422_){
_start:
{
uint8_t v___x_3423_; 
v___x_3423_ = lean_usize_dec_lt(v_i_3421_, v_sz_3420_);
if (v___x_3423_ == 0)
{
return v_bs_3422_;
}
else
{
lean_object* v_v_3424_; lean_object* v_proof_3425_; lean_object* v___x_3426_; lean_object* v_bs_x27_3427_; size_t v___x_3428_; size_t v___x_3429_; lean_object* v___x_3430_; 
v_v_3424_ = lean_array_uget_borrowed(v_bs_3422_, v_i_3421_);
v_proof_3425_ = lean_ctor_get(v_v_3424_, 1);
lean_inc_ref(v_proof_3425_);
v___x_3426_ = lean_unsigned_to_nat(0u);
v_bs_x27_3427_ = lean_array_uset(v_bs_3422_, v_i_3421_, v___x_3426_);
v___x_3428_ = ((size_t)1ULL);
v___x_3429_ = lean_usize_add(v_i_3421_, v___x_3428_);
v___x_3430_ = lean_array_uset(v_bs_x27_3427_, v_i_3421_, v_proof_3425_);
v_i_3421_ = v___x_3429_;
v_bs_3422_ = v___x_3430_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_3432_, lean_object* v_i_3433_, lean_object* v_bs_3434_){
_start:
{
size_t v_sz_boxed_3435_; size_t v_i_boxed_3436_; lean_object* v_res_3437_; 
v_sz_boxed_3435_ = lean_unbox_usize(v_sz_3432_);
lean_dec(v_sz_3432_);
v_i_boxed_3436_ = lean_unbox_usize(v_i_3433_);
lean_dec(v_i_3433_);
v_res_3437_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_3435_, v_i_boxed_3436_, v_bs_3434_);
return v_res_3437_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3439_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_3440_ = l_Lean_stringToMessageData(v___x_3439_);
return v___x_3440_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_3443_ = l_Lean_stringToMessageData(v___x_3442_);
return v___x_3443_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3445_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_3446_ = l_Lean_stringToMessageData(v___x_3445_);
return v___x_3446_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_3449_ = l_Lean_stringToMessageData(v___x_3448_);
return v___x_3449_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_3452_ = l_Lean_stringToMessageData(v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_3453_, lean_object* v_monad_3454_, lean_object* v_thms_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
uint8_t v_errorOnMissingSpec_3462_; 
v_errorOnMissingSpec_3462_ = lean_ctor_get_uint8(v_a_3456_, sizeof(void*)*6 + 2);
if (v_errorOnMissingSpec_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3463_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_3463_, 0, v_prog_3453_);
lean_ctor_set(v___x_3463_, 1, v_monad_3454_);
lean_ctor_set(v___x_3463_, 2, v_thms_3455_);
v___x_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
return v___x_3465_;
}
else
{
lean_object* v___x_3466_; lean_object* v___x_3467_; uint8_t v___x_3468_; 
v___x_3466_ = lean_array_get_size(v_thms_3455_);
v___x_3467_ = lean_unsigned_to_nat(0u);
v___x_3468_ = lean_nat_dec_eq(v___x_3466_, v___x_3467_);
if (v___x_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; size_t v_sz_3478_; size_t v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3469_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_3470_ = l_Lean_MessageData_ofExpr(v_monad_3454_);
v___x_3471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3469_);
lean_ctor_set(v___x_3471_, 1, v___x_3470_);
v___x_3472_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_3473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3471_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = l_Lean_MessageData_ofExpr(v_prog_3453_);
v___x_3475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3473_);
lean_ctor_set(v___x_3475_, 1, v___x_3474_);
v___x_3476_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_3477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v_sz_3478_ = lean_array_size(v_thms_3455_);
v___x_3479_ = ((size_t)0ULL);
v___x_3480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_3478_, v___x_3479_, v_thms_3455_);
v___x_3481_ = lean_array_to_list(v___x_3480_);
v___x_3482_ = lean_box(0);
v___x_3483_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_3481_, v___x_3482_);
v___x_3484_ = l_Lean_MessageData_ofList(v___x_3483_);
v___x_3485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3477_);
lean_ctor_set(v___x_3485_, 1, v___x_3484_);
v___x_3486_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3487_, 0, v___x_3485_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
v___x_3488_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3487_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_dec_ref(v_thms_3455_);
lean_dec_ref(v_monad_3454_);
v___x_3489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_3490_ = l_Lean_MessageData_ofExpr(v_prog_3453_);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3493_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_);
return v___x_3494_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_3495_, lean_object* v_monad_3496_, lean_object* v_thms_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3495_, v_monad_3496_, v_thms_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
lean_dec(v_a_3500_);
lean_dec_ref(v_a_3499_);
lean_dec_ref(v_a_3498_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_3505_, lean_object* v_monad_3506_, lean_object* v_thms_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3505_, v_monad_3506_, v_thms_3507_, v_a_3508_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_3521_, lean_object* v_monad_3522_, lean_object* v_thms_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(v_prog_3521_, v_monad_3522_, v_thms_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec_ref(v_a_3524_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(lean_object* v_scope_3537_, lean_object* v_prog_3538_, lean_object* v_monad_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_){
_start:
{
lean_object* v_specs_3548_; lean_object* v_jps_3549_; lean_object* v_lastLiftedPre_x3f_3550_; lean_object* v_nextDeclIdx_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3620_; 
v_specs_3548_ = lean_ctor_get(v_scope_3537_, 0);
v_jps_3549_ = lean_ctor_get(v_scope_3537_, 1);
v_lastLiftedPre_x3f_3550_ = lean_ctor_get(v_scope_3537_, 2);
v_nextDeclIdx_3551_ = lean_ctor_get(v_scope_3537_, 3);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_scope_3537_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3553_ = v_scope_3537_;
v_isShared_3554_ = v_isSharedCheck_3620_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_nextDeclIdx_3551_);
lean_inc(v_lastLiftedPre_x3f_3550_);
lean_inc(v_jps_3549_);
lean_inc(v_specs_3548_);
lean_dec(v_scope_3537_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3620_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; 
lean_inc_ref(v_prog_3538_);
v___x_3555_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(v_specs_3548_, v_prog_3538_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3611_; 
v_a_3556_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3558_ = v___x_3555_;
v_isShared_3559_ = v_isSharedCheck_3611_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3555_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3611_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v_fst_3560_; lean_object* v_snd_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3610_; 
v_fst_3560_ = lean_ctor_get(v_a_3556_, 0);
v_snd_3561_ = lean_ctor_get(v_a_3556_, 1);
v_isSharedCheck_3610_ = !lean_is_exclusive(v_a_3556_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3563_ = v_a_3556_;
v_isShared_3564_ = v_isSharedCheck_3610_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_snd_3561_);
lean_inc(v_fst_3560_);
lean_dec(v_a_3556_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3610_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v_snd_3561_);
v___x_3566_ = v___x_3553_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_snd_3561_);
lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_jps_3549_);
lean_ctor_set(v_reuseFailAlloc_3609_, 2, v_lastLiftedPre_x3f_3550_);
lean_ctor_set(v_reuseFailAlloc_3609_, 3, v_nextDeclIdx_3551_);
v___x_3566_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
if (lean_obj_tag(v_fst_3560_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3594_; 
lean_del_object(v___x_3558_);
v_a_3567_ = lean_ctor_get(v_fst_3560_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v_fst_3560_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3569_ = v_fst_3560_;
v_isShared_3570_ = v_isSharedCheck_3594_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v_fst_3560_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3594_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; 
v___x_3571_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3538_, v_monad_3539_, v_a_3567_, v_a_3540_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3585_; 
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3585_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3585_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v_a_3572_);
v___x_3577_ = v___x_3569_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3579_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3577_);
lean_ctor_set(v___x_3563_, 0, v___x_3566_);
v___x_3579_ = v___x_3563_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3581_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3579_);
v___x_3581_ = v___x_3574_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3579_);
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
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_del_object(v___x_3569_);
lean_dec_ref(v___x_3566_);
lean_del_object(v___x_3563_);
v_a_3586_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3571_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3571_);
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
}
else
{
lean_object* v_a_3595_; lean_object* v___x_3597_; uint8_t v_isShared_3598_; uint8_t v_isSharedCheck_3608_; 
lean_dec_ref(v_monad_3539_);
lean_dec_ref(v_prog_3538_);
v_a_3595_ = lean_ctor_get(v_fst_3560_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_fst_3560_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3597_ = v_fst_3560_;
v_isShared_3598_ = v_isSharedCheck_3608_;
goto v_resetjp_3596_;
}
else
{
lean_inc(v_a_3595_);
lean_dec(v_fst_3560_);
v___x_3597_ = lean_box(0);
v_isShared_3598_ = v_isSharedCheck_3608_;
goto v_resetjp_3596_;
}
v_resetjp_3596_:
{
lean_object* v___x_3600_; 
if (v_isShared_3598_ == 0)
{
v___x_3600_ = v___x_3597_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_a_3595_);
v___x_3600_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3602_; 
if (v_isShared_3564_ == 0)
{
lean_ctor_set(v___x_3563_, 1, v___x_3600_);
lean_ctor_set(v___x_3563_, 0, v___x_3566_);
v___x_3602_ = v___x_3563_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3606_, 1, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3604_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3602_);
v___x_3604_ = v___x_3558_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
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
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_del_object(v___x_3553_);
lean_dec(v_nextDeclIdx_3551_);
lean_dec(v_lastLiftedPre_x3f_3550_);
lean_dec(v_jps_3549_);
lean_dec_ref(v_monad_3539_);
lean_dec_ref(v_prog_3538_);
v_a_3612_ = lean_ctor_get(v___x_3555_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3555_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3555_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg___boxed(lean_object* v_scope_3621_, lean_object* v_prog_3622_, lean_object* v_monad_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(v_scope_3621_, v_prog_3622_, v_monad_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3625_);
lean_dec_ref(v_a_3624_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec(lean_object* v_scope_3633_, lean_object* v_prog_3634_, lean_object* v_monad_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(v_scope_3633_, v_prog_3634_, v_monad_3635_, v_a_3636_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___boxed(lean_object* v_scope_3649_, lean_object* v_prog_3650_, lean_object* v_monad_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec(v_scope_3649_, v_prog_3650_, v_monad_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
lean_dec(v_a_3662_);
lean_dec_ref(v_a_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3659_);
lean_dec(v_a_3658_);
lean_dec_ref(v_a_3657_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
lean_dec(v_a_3654_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
if (lean_obj_tag(v_a_3665_) == 0)
{
lean_object* v___x_3667_; 
v___x_3667_ = l_List_reverse___redArg(v_a_3666_);
return v___x_3667_;
}
else
{
lean_object* v_head_3668_; lean_object* v_tail_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3678_; 
v_head_3668_ = lean_ctor_get(v_a_3665_, 0);
v_tail_3669_ = lean_ctor_get(v_a_3665_, 1);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3665_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3671_ = v_a_3665_;
v_isShared_3672_ = v_isSharedCheck_3678_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_tail_3669_);
lean_inc(v_head_3668_);
lean_dec(v_a_3665_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3678_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3673_ = l_Lean_MessageData_ofExpr(v_head_3668_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 1, v_a_3666_);
lean_ctor_set(v___x_3671_, 0, v___x_3673_);
v___x_3675_ = v___x_3671_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v_a_3666_);
v___x_3675_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
v_a_3665_ = v_tail_3669_;
v_a_3666_ = v___x_3675_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
v___x_3680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_3681_ = l_Lean_stringToMessageData(v___x_3680_);
return v___x_3681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_3684_ = l_Lean_stringToMessageData(v___x_3683_);
return v___x_3684_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3686_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_3687_ = l_Lean_stringToMessageData(v___x_3686_);
return v___x_3687_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3689_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_3690_ = l_Lean_stringToMessageData(v___x_3689_);
return v___x_3690_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_3693_ = l_Lean_stringToMessageData(v___x_3692_);
return v___x_3693_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_3696_ = l_Lean_stringToMessageData(v___x_3695_);
return v___x_3696_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_3702_ = l_Lean_stringToMessageData(v___x_3701_);
return v___x_3702_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3704_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_3705_ = l_Lean_stringToMessageData(v___x_3704_);
return v___x_3705_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_3708_ = l_Lean_stringToMessageData(v___x_3707_);
return v___x_3708_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_scope_3712_, lean_object* v_goal_3713_, lean_object* v_info_3714_, lean_object* v_thm_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; uint8_t v___y_3922_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v_options_3969_; uint8_t v_hasTrace_3970_; 
v_options_3969_ = lean_ctor_get(v_a_3725_, 2);
v_hasTrace_3970_ = lean_ctor_get_uint8(v_options_3969_, sizeof(void*)*1);
if (v_hasTrace_3970_ == 0)
{
v___y_3954_ = v_a_3716_;
v___y_3955_ = v_a_3717_;
v___y_3956_ = v_a_3718_;
v___y_3957_ = v_a_3719_;
v___y_3958_ = v_a_3720_;
v___y_3959_ = v_a_3721_;
v___y_3960_ = v_a_3722_;
v___y_3961_ = v_a_3723_;
v___y_3962_ = v_a_3724_;
v___y_3963_ = v_a_3725_;
v___y_3964_ = v_a_3726_;
goto v___jp_3953_;
}
else
{
lean_object* v_inheritedTraceOptions_3971_; lean_object* v_cls_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v_inheritedTraceOptions_3971_ = lean_ctor_get(v_a_3725_, 13);
v_cls_3972_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3973_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3971_, v_options_3969_, v___x_3973_);
if (v___x_3974_ == 0)
{
v___y_3954_ = v_a_3716_;
v___y_3955_ = v_a_3717_;
v___y_3956_ = v_a_3718_;
v___y_3957_ = v_a_3719_;
v___y_3958_ = v_a_3720_;
v___y_3959_ = v_a_3721_;
v___y_3960_ = v_a_3722_;
v___y_3961_ = v_a_3723_;
v___y_3962_ = v_a_3724_;
v___y_3963_ = v_a_3725_;
v___y_3964_ = v_a_3726_;
goto v___jp_3953_;
}
else
{
lean_object* v_proof_3975_; lean_object* v___x_3976_; lean_object* v___y_3978_; 
v_proof_3975_ = lean_ctor_get(v_thm_3715_, 1);
v___x_3976_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
switch(lean_obj_tag(v_proof_3975_))
{
case 0:
{
lean_object* v_declName_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_declName_4002_ = lean_ctor_get(v_proof_3975_, 0);
v___x_4003_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_4002_);
v___x_4004_ = l_Lean_MessageData_ofName(v_declName_4002_);
v___x_4005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4005_, 0, v___x_4003_);
lean_ctor_set(v___x_4005_, 1, v___x_4004_);
v___y_3978_ = v___x_4005_;
goto v___jp_3977_;
}
case 1:
{
lean_object* v_fvarId_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_fvarId_4006_ = lean_ctor_get(v_proof_3975_, 0);
v___x_4007_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_4006_);
v___x_4008_ = l_Lean_mkFVar(v_fvarId_4006_);
v___x_4009_ = l_Lean_MessageData_ofExpr(v___x_4008_);
v___x_4010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4007_);
lean_ctor_set(v___x_4010_, 1, v___x_4009_);
v___y_3978_ = v___x_4010_;
goto v___jp_3977_;
}
default: 
{
lean_object* v_ref_4011_; lean_object* v_proof_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_ref_4011_ = lean_ctor_get(v_proof_3975_, 1);
v_proof_4012_ = lean_ctor_get(v_proof_3975_, 2);
v___x_4013_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_4011_);
v___x_4014_ = l_Lean_MessageData_ofSyntax(v_ref_4011_);
v___x_4015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4013_);
lean_ctor_set(v___x_4015_, 1, v___x_4014_);
v___x_4016_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_4017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4015_);
lean_ctor_set(v___x_4017_, 1, v___x_4016_);
lean_inc_ref(v_proof_4012_);
v___x_4018_ = l_Lean_MessageData_ofExpr(v_proof_4012_);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4017_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___y_3978_ = v___x_4019_;
goto v___jp_3977_;
}
}
v___jp_3977_:
{
lean_object* v_excessArgs_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_excessArgs_3979_ = lean_ctor_get(v_info_3714_, 2);
v___x_3980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3976_);
lean_ctor_set(v___x_3980_, 1, v___y_3978_);
v___x_3981_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3980_);
lean_ctor_set(v___x_3982_, 1, v___x_3981_);
v___x_3983_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3714_);
v___x_3984_ = l_Lean_MessageData_ofExpr(v___x_3983_);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3982_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_3987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3985_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
lean_inc_ref(v_excessArgs_3979_);
v___x_3988_ = lean_array_to_list(v_excessArgs_3979_);
v___x_3989_ = lean_box(0);
v___x_3990_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3988_, v___x_3989_);
v___x_3991_ = l_Lean_MessageData_ofList(v___x_3990_);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3987_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3972_, v___x_3992_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_dec_ref_known(v___x_3993_, 1);
v___y_3954_ = v_a_3716_;
v___y_3955_ = v_a_3717_;
v___y_3956_ = v_a_3718_;
v___y_3957_ = v_a_3719_;
v___y_3958_ = v_a_3720_;
v___y_3959_ = v_a_3721_;
v___y_3960_ = v_a_3722_;
v___y_3961_ = v_a_3723_;
v___y_3962_ = v_a_3724_;
v___y_3963_ = v_a_3725_;
v___y_3964_ = v_a_3726_;
goto v___jp_3953_;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
lean_dec(v_goal_3713_);
lean_dec_ref(v_scope_3712_);
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3993_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3993_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
}
v___jp_3728_:
{
lean_object* v_excessArgs_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_excessArgs_3738_ = lean_ctor_get(v_info_3714_, 2);
lean_inc_ref(v_excessArgs_3738_);
lean_inc_ref(v___y_3733_);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___y_3733_);
lean_ctor_set(v___x_3739_, 1, v___y_3737_);
v___x_3740_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3741_);
lean_ctor_set(v___x_3742_, 1, v___y_3729_);
v___x_3743_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3742_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l_Lean_indentExpr(v___y_3732_);
v___x_3746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3746_, 0, v___x_3744_);
lean_ctor_set(v___x_3746_, 1, v___x_3745_);
v___x_3747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_3714_);
lean_dec_ref(v_info_3714_);
v___x_3750_ = l_Lean_indentExpr(v___x_3749_);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3748_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = lean_array_to_list(v_excessArgs_3738_);
v___x_3755_ = lean_box(0);
v___x_3756_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3754_, v___x_3755_);
v___x_3757_ = l_Lean_MessageData_ofList(v___x_3756_);
v___x_3758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3753_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = l_Lean_indentExpr(v___y_3731_);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3762_, v___y_3734_, v___y_3730_, v___y_3735_, v___y_3736_);
return v___x_3763_;
}
v___jp_3764_:
{
if (lean_obj_tag(v___y_3776_) == 0)
{
lean_object* v_a_3777_; 
v_a_3777_ = lean_ctor_get(v___y_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___y_3776_, 1);
if (lean_obj_tag(v_a_3777_) == 1)
{
lean_object* v_val_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3849_; 
v_val_3778_ = lean_ctor_get(v_a_3777_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v_a_3777_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3780_ = v_a_3777_;
v_isShared_3781_ = v_isSharedCheck_3849_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_val_3778_);
lean_dec(v_a_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3849_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3787_; 
v___x_3782_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
v___x_3783_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3714_);
v___x_3784_ = l_Lean_indentExpr(v___x_3783_);
lean_inc_ref(v___x_3784_);
v___x_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3785_, 0, v___x_3782_);
lean_ctor_set(v___x_3785_, 1, v___x_3784_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v___x_3785_);
v___x_3787_ = v___x_3780_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3788_; 
lean_inc(v_goal_3713_);
lean_inc(v_val_3778_);
v___x_3788_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_3778_, v_goal_3713_, v___x_3787_, v___y_3765_, v___y_3769_, v___y_3773_, v___y_3768_, v___y_3767_, v___y_3771_, v___y_3770_, v___y_3772_, v___y_3766_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_object* v_a_3789_; lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3839_; 
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3791_ = v___x_3788_;
v_isShared_3792_ = v_isSharedCheck_3839_;
goto v_resetjp_3790_;
}
else
{
lean_inc(v_a_3789_);
lean_dec(v___x_3788_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3839_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
if (lean_obj_tag(v_a_3789_) == 1)
{
lean_object* v_mvarIds_3793_; lean_object* v___x_3794_; lean_object* v___x_3796_; 
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3778_);
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
lean_dec(v_goal_3713_);
v_mvarIds_3793_ = lean_ctor_get(v_a_3789_, 0);
lean_inc(v_mvarIds_3793_);
lean_dec_ref_known(v_a_3789_, 1);
v___x_3794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3794_, 0, v_scope_3712_);
lean_ctor_set(v___x_3794_, 1, v_mvarIds_3793_);
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3794_);
v___x_3796_ = v___x_3791_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v___x_3794_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
else
{
lean_object* v_expr_3798_; lean_object* v___x_3799_; 
lean_del_object(v___x_3791_);
lean_dec(v_a_3789_);
lean_dec_ref(v_scope_3712_);
v_expr_3798_ = lean_ctor_get(v_val_3778_, 0);
lean_inc_ref(v_expr_3798_);
lean_dec(v_val_3778_);
lean_inc(v___y_3775_);
lean_inc_ref(v___y_3774_);
lean_inc(v___y_3766_);
lean_inc_ref(v___y_3772_);
v___x_3799_ = lean_infer_type(v_expr_3798_, v___y_3772_, v___y_3766_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3801_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3799_, 1);
v___x_3801_ = l_Lean_MVarId_getType(v_goal_3713_, v___y_3772_, v___y_3766_, v___y_3774_, v___y_3775_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v_proof_3803_; lean_object* v___x_3804_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v_proof_3803_ = lean_ctor_get(v_thm_3715_, 1);
lean_inc_ref(v_proof_3803_);
lean_dec_ref(v_thm_3715_);
v___x_3804_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
switch(lean_obj_tag(v_proof_3803_))
{
case 0:
{
lean_object* v_declName_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v_declName_3805_ = lean_ctor_get(v_proof_3803_, 0);
lean_inc(v_declName_3805_);
lean_dec_ref_known(v_proof_3803_, 1);
v___x_3806_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3807_ = l_Lean_MessageData_ofName(v_declName_3805_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___y_3729_ = v___x_3784_;
v___y_3730_ = v___y_3766_;
v___y_3731_ = v_a_3800_;
v___y_3732_ = v_a_3802_;
v___y_3733_ = v___x_3804_;
v___y_3734_ = v___y_3772_;
v___y_3735_ = v___y_3774_;
v___y_3736_ = v___y_3775_;
v___y_3737_ = v___x_3808_;
goto v___jp_3728_;
}
case 1:
{
lean_object* v_fvarId_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_fvarId_3809_ = lean_ctor_get(v_proof_3803_, 0);
lean_inc(v_fvarId_3809_);
lean_dec_ref_known(v_proof_3803_, 1);
v___x_3810_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3811_ = l_Lean_mkFVar(v_fvarId_3809_);
v___x_3812_ = l_Lean_MessageData_ofExpr(v___x_3811_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3810_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___y_3729_ = v___x_3784_;
v___y_3730_ = v___y_3766_;
v___y_3731_ = v_a_3800_;
v___y_3732_ = v_a_3802_;
v___y_3733_ = v___x_3804_;
v___y_3734_ = v___y_3772_;
v___y_3735_ = v___y_3774_;
v___y_3736_ = v___y_3775_;
v___y_3737_ = v___x_3813_;
goto v___jp_3728_;
}
default: 
{
lean_object* v_ref_3814_; lean_object* v_proof_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_ref_3814_ = lean_ctor_get(v_proof_3803_, 1);
lean_inc(v_ref_3814_);
v_proof_3815_ = lean_ctor_get(v_proof_3803_, 2);
lean_inc_ref(v_proof_3815_);
lean_dec_ref_known(v_proof_3803_, 3);
v___x_3816_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3817_ = l_Lean_MessageData_ofSyntax(v_ref_3814_);
v___x_3818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3817_);
v___x_3819_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = l_Lean_MessageData_ofExpr(v_proof_3815_);
v___x_3822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___y_3729_ = v___x_3784_;
v___y_3730_ = v___y_3766_;
v___y_3731_ = v_a_3800_;
v___y_3732_ = v_a_3802_;
v___y_3733_ = v___x_3804_;
v___y_3734_ = v___y_3772_;
v___y_3735_ = v___y_3774_;
v___y_3736_ = v___y_3775_;
v___y_3737_ = v___x_3822_;
goto v___jp_3728_;
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec(v_a_3800_);
lean_dec_ref(v___x_3784_);
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
v_a_3823_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3801_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3801_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref(v___x_3784_);
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
lean_dec(v_goal_3713_);
v_a_3831_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3799_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3799_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v___x_3784_);
lean_dec(v_val_3778_);
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
lean_dec(v_goal_3713_);
lean_dec_ref(v_scope_3712_);
v_a_3840_ = lean_ctor_get(v___x_3788_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3788_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3788_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
}
}
else
{
lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v_a_3777_);
lean_dec(v_goal_3713_);
lean_dec_ref(v_scope_3712_);
v___x_3850_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3714_);
v___x_3851_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_3714_);
lean_dec_ref(v_info_3714_);
v___x_3852_ = lean_unsigned_to_nat(1u);
v___x_3853_ = lean_mk_empty_array_with_capacity(v___x_3852_);
v___x_3854_ = lean_array_push(v___x_3853_, v_thm_3715_);
v___x_3855_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3850_, v___x_3851_, v___x_3854_, v___y_3765_, v___y_3772_, v___y_3766_, v___y_3774_, v___y_3775_);
return v___x_3855_;
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
lean_dec(v_goal_3713_);
lean_dec_ref(v_scope_3712_);
v_a_3856_ = lean_ctor_get(v___y_3776_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___y_3776_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___y_3776_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___y_3776_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
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
v___jp_3864_:
{
lean_object* v_excessArgs_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_excessArgs_3880_ = lean_ctor_get(v_info_3714_, 2);
lean_inc_ref(v___y_3877_);
v___x_3881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___y_3877_);
lean_ctor_set(v___x_3881_, 1, v___y_3879_);
v___x_3882_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3881_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_3714_);
v___x_3885_ = l_Lean_indentExpr(v___x_3884_);
v___x_3886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3883_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = l_Lean_Exception_toMessageData(v___y_3872_);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = l_Lean_indentExpr(v___y_3873_);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
v___x_3897_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_3714_);
v___x_3898_ = l_Lean_indentExpr(v___x_3897_);
v___x_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3896_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
v___x_3900_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
lean_inc_ref(v_excessArgs_3880_);
v___x_3902_ = lean_array_to_list(v_excessArgs_3880_);
v___x_3903_ = lean_box(0);
v___x_3904_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3902_, v___x_3903_);
v___x_3905_ = l_Lean_MessageData_ofList(v___x_3904_);
v___x_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3901_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
v___x_3907_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3906_, v___y_3878_, v___y_3865_, v___y_3869_, v___y_3870_);
v___y_3765_ = v___y_3871_;
v___y_3766_ = v___y_3865_;
v___y_3767_ = v___y_3866_;
v___y_3768_ = v___y_3874_;
v___y_3769_ = v___y_3875_;
v___y_3770_ = v___y_3876_;
v___y_3771_ = v___y_3867_;
v___y_3772_ = v___y_3878_;
v___y_3773_ = v___y_3868_;
v___y_3774_ = v___y_3869_;
v___y_3775_ = v___y_3870_;
v___y_3776_ = v___x_3907_;
goto v___jp_3764_;
}
v___jp_3908_:
{
if (v___y_3922_ == 0)
{
lean_object* v___x_3923_; 
lean_dec_ref(v___y_3912_);
lean_inc(v_goal_3713_);
v___x_3923_ = l_Lean_MVarId_getType(v_goal_3713_, v___y_3921_, v___y_3909_, v___y_3914_, v___y_3915_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v_proof_3925_; lean_object* v___x_3926_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v_proof_3925_ = lean_ctor_get(v_thm_3715_, 1);
v___x_3926_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
switch(lean_obj_tag(v_proof_3925_))
{
case 0:
{
lean_object* v_declName_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; 
v_declName_3927_ = lean_ctor_get(v_proof_3925_, 0);
v___x_3928_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3927_);
v___x_3929_ = l_Lean_MessageData_ofName(v_declName_3927_);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___y_3865_ = v___y_3909_;
v___y_3866_ = v___y_3910_;
v___y_3867_ = v___y_3911_;
v___y_3868_ = v___y_3913_;
v___y_3869_ = v___y_3914_;
v___y_3870_ = v___y_3915_;
v___y_3871_ = v___y_3916_;
v___y_3872_ = v___y_3917_;
v___y_3873_ = v_a_3924_;
v___y_3874_ = v___y_3918_;
v___y_3875_ = v___y_3919_;
v___y_3876_ = v___y_3920_;
v___y_3877_ = v___x_3926_;
v___y_3878_ = v___y_3921_;
v___y_3879_ = v___x_3930_;
goto v___jp_3864_;
}
case 1:
{
lean_object* v_fvarId_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_fvarId_3931_ = lean_ctor_get(v_proof_3925_, 0);
v___x_3932_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3931_);
v___x_3933_ = l_Lean_mkFVar(v_fvarId_3931_);
v___x_3934_ = l_Lean_MessageData_ofExpr(v___x_3933_);
v___x_3935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3935_, 0, v___x_3932_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___y_3865_ = v___y_3909_;
v___y_3866_ = v___y_3910_;
v___y_3867_ = v___y_3911_;
v___y_3868_ = v___y_3913_;
v___y_3869_ = v___y_3914_;
v___y_3870_ = v___y_3915_;
v___y_3871_ = v___y_3916_;
v___y_3872_ = v___y_3917_;
v___y_3873_ = v_a_3924_;
v___y_3874_ = v___y_3918_;
v___y_3875_ = v___y_3919_;
v___y_3876_ = v___y_3920_;
v___y_3877_ = v___x_3926_;
v___y_3878_ = v___y_3921_;
v___y_3879_ = v___x_3935_;
goto v___jp_3864_;
}
default: 
{
lean_object* v_ref_3936_; lean_object* v_proof_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v_ref_3936_ = lean_ctor_get(v_proof_3925_, 1);
v_proof_3937_ = lean_ctor_get(v_proof_3925_, 2);
v___x_3938_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3936_);
v___x_3939_ = l_Lean_MessageData_ofSyntax(v_ref_3936_);
v___x_3940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3938_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
v___x_3941_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3942_, 0, v___x_3940_);
lean_ctor_set(v___x_3942_, 1, v___x_3941_);
lean_inc_ref(v_proof_3937_);
v___x_3943_ = l_Lean_MessageData_ofExpr(v_proof_3937_);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
v___y_3865_ = v___y_3909_;
v___y_3866_ = v___y_3910_;
v___y_3867_ = v___y_3911_;
v___y_3868_ = v___y_3913_;
v___y_3869_ = v___y_3914_;
v___y_3870_ = v___y_3915_;
v___y_3871_ = v___y_3916_;
v___y_3872_ = v___y_3917_;
v___y_3873_ = v_a_3924_;
v___y_3874_ = v___y_3918_;
v___y_3875_ = v___y_3919_;
v___y_3876_ = v___y_3920_;
v___y_3877_ = v___x_3926_;
v___y_3878_ = v___y_3921_;
v___y_3879_ = v___x_3944_;
goto v___jp_3864_;
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v___y_3917_);
lean_dec_ref(v_thm_3715_);
lean_dec_ref(v_info_3714_);
lean_dec(v_goal_3713_);
lean_dec_ref(v_scope_3712_);
v_a_3945_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3923_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3923_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_dec_ref(v___y_3917_);
v___y_3765_ = v___y_3916_;
v___y_3766_ = v___y_3909_;
v___y_3767_ = v___y_3910_;
v___y_3768_ = v___y_3918_;
v___y_3769_ = v___y_3919_;
v___y_3770_ = v___y_3920_;
v___y_3771_ = v___y_3911_;
v___y_3772_ = v___y_3921_;
v___y_3773_ = v___y_3913_;
v___y_3774_ = v___y_3914_;
v___y_3775_ = v___y_3915_;
v___y_3776_ = v___y_3912_;
goto v___jp_3764_;
}
}
v___jp_3953_:
{
lean_object* v___x_3965_; 
lean_inc_ref(v_info_3714_);
lean_inc_ref(v_thm_3715_);
v___x_3965_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v_thm_3715_, v_info_3714_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_, v___y_3963_, v___y_3964_);
if (lean_obj_tag(v___x_3965_) == 0)
{
v___y_3765_ = v___y_3954_;
v___y_3766_ = v___y_3962_;
v___y_3767_ = v___y_3958_;
v___y_3768_ = v___y_3957_;
v___y_3769_ = v___y_3955_;
v___y_3770_ = v___y_3960_;
v___y_3771_ = v___y_3959_;
v___y_3772_ = v___y_3961_;
v___y_3773_ = v___y_3956_;
v___y_3774_ = v___y_3963_;
v___y_3775_ = v___y_3964_;
v___y_3776_ = v___x_3965_;
goto v___jp_3764_;
}
else
{
lean_object* v_a_3966_; uint8_t v___x_3967_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
v___x_3967_ = l_Lean_Exception_isInterrupt(v_a_3966_);
if (v___x_3967_ == 0)
{
uint8_t v___x_3968_; 
lean_inc(v_a_3966_);
v___x_3968_ = l_Lean_Exception_isRuntime(v_a_3966_);
v___y_3909_ = v___y_3962_;
v___y_3910_ = v___y_3958_;
v___y_3911_ = v___y_3959_;
v___y_3912_ = v___x_3965_;
v___y_3913_ = v___y_3956_;
v___y_3914_ = v___y_3963_;
v___y_3915_ = v___y_3964_;
v___y_3916_ = v___y_3954_;
v___y_3917_ = v_a_3966_;
v___y_3918_ = v___y_3957_;
v___y_3919_ = v___y_3955_;
v___y_3920_ = v___y_3960_;
v___y_3921_ = v___y_3961_;
v___y_3922_ = v___x_3968_;
goto v___jp_3908_;
}
else
{
v___y_3909_ = v___y_3962_;
v___y_3910_ = v___y_3958_;
v___y_3911_ = v___y_3959_;
v___y_3912_ = v___x_3965_;
v___y_3913_ = v___y_3956_;
v___y_3914_ = v___y_3963_;
v___y_3915_ = v___y_3964_;
v___y_3916_ = v___y_3954_;
v___y_3917_ = v_a_3966_;
v___y_3918_ = v___y_3957_;
v___y_3919_ = v___y_3955_;
v___y_3920_ = v___y_3960_;
v___y_3921_ = v___y_3961_;
v___y_3922_ = v___x_3967_;
goto v___jp_3908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object* v_scope_4020_, lean_object* v_goal_4021_, lean_object* v_info_4022_, lean_object* v_thm_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_4020_, v_goal_4021_, v_info_4022_, v_thm_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_);
lean_dec(v_a_4034_);
lean_dec_ref(v_a_4033_);
lean_dec(v_a_4032_);
lean_dec_ref(v_a_4031_);
lean_dec(v_a_4030_);
lean_dec_ref(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
return v_res_4036_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_4039_ = l_Lean_stringToMessageData(v___x_4038_);
return v___x_4039_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(lean_object* v_prog_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_untilPat_x3f_4052_; 
v_untilPat_x3f_4052_ = lean_ctor_get(v_a_4044_, 5);
if (lean_obj_tag(v_untilPat_x3f_4052_) == 1)
{
lean_object* v_val_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; 
v_val_4053_ = lean_ctor_get(v_untilPat_x3f_4052_, 0);
v___x_4054_ = 1;
lean_inc_ref(v_prog_4043_);
lean_inc(v_val_4053_);
v___x_4055_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_val_4053_, v_prog_4043_, v___x_4054_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4102_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4058_ = v___x_4055_;
v_isShared_4059_ = v_isSharedCheck_4102_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4055_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4102_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
if (lean_obj_tag(v_a_4056_) == 0)
{
uint8_t v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4063_; 
lean_dec_ref(v_prog_4043_);
v___x_4060_ = 0;
v___x_4061_ = lean_box(v___x_4060_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4061_);
v___x_4063_ = v___x_4058_;
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
lean_object* v_options_4065_; uint8_t v_hasTrace_4066_; 
lean_dec_ref_known(v_a_4056_, 1);
v_options_4065_ = lean_ctor_get(v_a_4049_, 2);
v_hasTrace_4066_ = lean_ctor_get_uint8(v_options_4065_, sizeof(void*)*1);
if (v_hasTrace_4066_ == 0)
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
lean_dec_ref(v_prog_4043_);
v___x_4067_ = lean_box(v___x_4054_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4067_);
v___x_4069_ = v___x_4058_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; uint8_t v___x_4074_; 
v_inheritedTraceOptions_4071_ = lean_ctor_get(v_a_4049_, 13);
v___x_4072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4073_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4074_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4071_, v_options_4065_, v___x_4073_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4077_; 
lean_dec_ref(v_prog_4043_);
v___x_4075_ = lean_box(v___x_4054_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 0, v___x_4075_);
v___x_4077_ = v___x_4058_;
goto v_reusejp_4076_;
}
else
{
lean_object* v_reuseFailAlloc_4078_; 
v_reuseFailAlloc_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4078_, 0, v___x_4075_);
v___x_4077_ = v_reuseFailAlloc_4078_;
goto v_reusejp_4076_;
}
v_reusejp_4076_:
{
return v___x_4077_;
}
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_del_object(v___x_4058_);
v___x_4079_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_4080_ = l_Lean_MessageData_ofExpr(v_prog_4043_);
v___x_4081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4079_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_4083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4081_);
lean_ctor_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4072_, v___x_4083_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4092_; 
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v___x_4084_, 0);
lean_dec(v_unused_4093_);
v___x_4086_ = v___x_4084_;
v_isShared_4087_ = v_isSharedCheck_4092_;
goto v_resetjp_4085_;
}
else
{
lean_dec(v___x_4084_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4092_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4088_ = lean_box(v___x_4054_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set(v___x_4086_, 0, v___x_4088_);
v___x_4090_ = v___x_4086_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
v_a_4094_ = lean_ctor_get(v___x_4084_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4084_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4084_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
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
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec_ref(v_prog_4043_);
v_a_4103_ = lean_ctor_get(v___x_4055_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4055_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4055_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
uint8_t v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec_ref(v_prog_4043_);
v___x_4111_ = 0;
v___x_4112_ = lean_box(v___x_4111_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_prog_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_prog_4114_, v_a_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_, v_a_4121_);
lean_dec(v_a_4121_);
lean_dec_ref(v_a_4120_);
lean_dec(v_a_4119_);
lean_dec_ref(v_a_4118_);
lean_dec(v_a_4117_);
lean_dec_ref(v_a_4116_);
lean_dec_ref(v_a_4115_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object* v_prog_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_){
_start:
{
lean_object* v___x_4137_; 
v___x_4137_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_prog_4124_, v_a_4125_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_, v_a_4135_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object* v_prog_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v_prog_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
lean_dec(v_a_4149_);
lean_dec_ref(v_a_4148_);
lean_dec(v_a_4147_);
lean_dec_ref(v_a_4146_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v_b_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
lean_object* v___x_4166_; 
lean_inc(v___y_4164_);
lean_inc_ref(v___y_4163_);
lean_inc(v___y_4162_);
lean_inc_ref(v___y_4161_);
lean_inc(v___y_4159_);
lean_inc_ref(v___y_4158_);
lean_inc(v___y_4157_);
lean_inc_ref(v___y_4156_);
lean_inc(v___y_4155_);
lean_inc(v___y_4154_);
lean_inc_ref(v___y_4153_);
v___x_4166_ = lean_apply_13(v_k_4152_, v_b_4160_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, lean_box(0));
return v___x_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v_b_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v_b_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4182_, lean_object* v_type_4183_, lean_object* v_val_4184_, lean_object* v_k_4185_, uint8_t v_nondep_4186_, uint8_t v_kind_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v___f_4200_; lean_object* v___x_4201_; 
lean_inc(v___y_4194_);
lean_inc_ref(v___y_4193_);
lean_inc(v___y_4192_);
lean_inc_ref(v___y_4191_);
lean_inc(v___y_4190_);
lean_inc(v___y_4189_);
lean_inc_ref(v___y_4188_);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4200_, 0, v_k_4185_);
lean_closure_set(v___f_4200_, 1, v___y_4188_);
lean_closure_set(v___f_4200_, 2, v___y_4189_);
lean_closure_set(v___f_4200_, 3, v___y_4190_);
lean_closure_set(v___f_4200_, 4, v___y_4191_);
lean_closure_set(v___f_4200_, 5, v___y_4192_);
lean_closure_set(v___f_4200_, 6, v___y_4193_);
lean_closure_set(v___f_4200_, 7, v___y_4194_);
v___x_4201_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4182_, v_type_4183_, v_val_4184_, v___f_4200_, v_nondep_4186_, v_kind_4187_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
if (lean_obj_tag(v___x_4201_) == 0)
{
return v___x_4201_;
}
else
{
lean_object* v_a_4202_; lean_object* v___x_4204_; uint8_t v_isShared_4205_; uint8_t v_isSharedCheck_4209_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4209_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4209_ == 0)
{
v___x_4204_ = v___x_4201_;
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
else
{
lean_inc(v_a_4202_);
lean_dec(v___x_4201_);
v___x_4204_ = lean_box(0);
v_isShared_4205_ = v_isSharedCheck_4209_;
goto v_resetjp_4203_;
}
v_resetjp_4203_:
{
lean_object* v___x_4207_; 
if (v_isShared_4205_ == 0)
{
v___x_4207_ = v___x_4204_;
goto v_reusejp_4206_;
}
else
{
lean_object* v_reuseFailAlloc_4208_; 
v_reuseFailAlloc_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4208_, 0, v_a_4202_);
v___x_4207_ = v_reuseFailAlloc_4208_;
goto v_reusejp_4206_;
}
v_reusejp_4206_:
{
return v___x_4207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4210_ = _args[0];
lean_object* v_type_4211_ = _args[1];
lean_object* v_val_4212_ = _args[2];
lean_object* v_k_4213_ = _args[3];
lean_object* v_nondep_4214_ = _args[4];
lean_object* v_kind_4215_ = _args[5];
lean_object* v___y_4216_ = _args[6];
lean_object* v___y_4217_ = _args[7];
lean_object* v___y_4218_ = _args[8];
lean_object* v___y_4219_ = _args[9];
lean_object* v___y_4220_ = _args[10];
lean_object* v___y_4221_ = _args[11];
lean_object* v___y_4222_ = _args[12];
lean_object* v___y_4223_ = _args[13];
lean_object* v___y_4224_ = _args[14];
lean_object* v___y_4225_ = _args[15];
lean_object* v___y_4226_ = _args[16];
lean_object* v___y_4227_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4228_; uint8_t v_kind_boxed_4229_; lean_object* v_res_4230_; 
v_nondep_boxed_4228_ = lean_unbox(v_nondep_4214_);
v_kind_boxed_4229_ = lean_unbox(v_kind_4215_);
v_res_4230_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4210_, v_type_4211_, v_val_4212_, v_k_4213_, v_nondep_boxed_4228_, v_kind_boxed_4229_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4231_, lean_object* v_name_4232_, lean_object* v_type_4233_, lean_object* v_val_4234_, lean_object* v_k_4235_, uint8_t v_nondep_4236_, uint8_t v_kind_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4232_, v_type_4233_, v_val_4234_, v_k_4235_, v_nondep_4236_, v_kind_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4251_ = _args[0];
lean_object* v_name_4252_ = _args[1];
lean_object* v_type_4253_ = _args[2];
lean_object* v_val_4254_ = _args[3];
lean_object* v_k_4255_ = _args[4];
lean_object* v_nondep_4256_ = _args[5];
lean_object* v_kind_4257_ = _args[6];
lean_object* v___y_4258_ = _args[7];
lean_object* v___y_4259_ = _args[8];
lean_object* v___y_4260_ = _args[9];
lean_object* v___y_4261_ = _args[10];
lean_object* v___y_4262_ = _args[11];
lean_object* v___y_4263_ = _args[12];
lean_object* v___y_4264_ = _args[13];
lean_object* v___y_4265_ = _args[14];
lean_object* v___y_4266_ = _args[15];
lean_object* v___y_4267_ = _args[16];
lean_object* v___y_4268_ = _args[17];
lean_object* v___y_4269_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4270_; uint8_t v_kind_boxed_4271_; lean_object* v_res_4272_; 
v_nondep_boxed_4270_ = lean_unbox(v_nondep_4256_);
v_kind_boxed_4271_ = lean_unbox(v_kind_4257_);
v_res_4272_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4251_, v_name_4252_, v_type_4253_, v_val_4254_, v_k_4255_, v_nondep_boxed_4270_, v_kind_boxed_4271_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_);
lean_dec(v___y_4268_);
lean_dec_ref(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec_ref(v___y_4265_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4273_, lean_object* v_declInfos_4274_, lean_object* v_k_4275_, lean_object* v_fv_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_){
_start:
{
lean_object* v_res_4289_; 
v_res_4289_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4273_, v_declInfos_4274_, v_k_4275_, v_fv_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
lean_dec(v___y_4283_);
lean_dec_ref(v___y_4282_);
lean_dec(v___y_4281_);
lean_dec_ref(v___y_4280_);
lean_dec(v___y_4279_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
return v_res_4289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4290_, lean_object* v_k_4291_, lean_object* v_acc_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; 
v___x_4305_ = lean_array_get_size(v_acc_4292_);
v___x_4306_ = lean_array_get_size(v_declInfos_4290_);
v___x_4307_ = lean_nat_dec_lt(v___x_4305_, v___x_4306_);
if (v___x_4307_ == 0)
{
lean_object* v___x_4308_; 
lean_dec_ref(v_declInfos_4290_);
lean_inc(v_a_4303_);
lean_inc_ref(v_a_4302_);
lean_inc(v_a_4301_);
lean_inc_ref(v_a_4300_);
lean_inc(v_a_4299_);
lean_inc_ref(v_a_4298_);
lean_inc(v_a_4297_);
lean_inc_ref(v_a_4296_);
lean_inc(v_a_4295_);
lean_inc(v_a_4294_);
lean_inc_ref(v_a_4293_);
v___x_4308_ = lean_apply_13(v_k_4291_, v_acc_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_, lean_box(0));
return v___x_4308_;
}
else
{
lean_object* v___x_4309_; lean_object* v_snd_4310_; lean_object* v_fst_4311_; lean_object* v_fst_4312_; lean_object* v_snd_4313_; lean_object* v___f_4314_; uint8_t v___x_4315_; uint8_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4309_ = lean_array_fget_borrowed(v_declInfos_4290_, v___x_4305_);
v_snd_4310_ = lean_ctor_get(v___x_4309_, 1);
v_fst_4311_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_fst_4311_);
v_fst_4312_ = lean_ctor_get(v_snd_4310_, 0);
lean_inc(v_fst_4312_);
v_snd_4313_ = lean_ctor_get(v_snd_4310_, 1);
lean_inc(v_snd_4313_);
v___f_4314_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4314_, 0, v_acc_4292_);
lean_closure_set(v___f_4314_, 1, v_declInfos_4290_);
lean_closure_set(v___f_4314_, 2, v_k_4291_);
v___x_4315_ = 0;
v___x_4316_ = 0;
v___x_4317_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4311_, v_fst_4312_, v_snd_4313_, v___f_4314_, v___x_4315_, v___x_4316_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_, v_a_4303_);
return v___x_4317_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4318_, lean_object* v_declInfos_4319_, lean_object* v_k_4320_, lean_object* v_fv_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4334_ = lean_array_push(v_acc_4318_, v_fv_4321_);
v___x_4335_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4319_, v_k_4320_, v___x_4334_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4336_, lean_object* v_k_4337_, lean_object* v_acc_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4336_, v_k_4337_, v_acc_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
lean_dec(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
return v_res_4351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4352_, lean_object* v_h__1_4353_){
_start:
{
lean_object* v_snd_4354_; lean_object* v_fst_4355_; lean_object* v_fst_4356_; lean_object* v_snd_4357_; lean_object* v___x_4358_; 
v_snd_4354_ = lean_ctor_get(v_x_4352_, 1);
lean_inc(v_snd_4354_);
v_fst_4355_ = lean_ctor_get(v_x_4352_, 0);
lean_inc(v_fst_4355_);
lean_dec_ref(v_x_4352_);
v_fst_4356_ = lean_ctor_get(v_snd_4354_, 0);
lean_inc(v_fst_4356_);
v_snd_4357_ = lean_ctor_get(v_snd_4354_, 1);
lean_inc(v_snd_4357_);
lean_dec(v_snd_4354_);
v___x_4358_ = lean_apply_3(v_h__1_4353_, v_fst_4355_, v_fst_4356_, v_snd_4357_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4359_, lean_object* v_x_4360_, lean_object* v_h__1_4361_){
_start:
{
lean_object* v_snd_4362_; lean_object* v_fst_4363_; lean_object* v_fst_4364_; lean_object* v_snd_4365_; lean_object* v___x_4366_; 
v_snd_4362_ = lean_ctor_get(v_x_4360_, 1);
lean_inc(v_snd_4362_);
v_fst_4363_ = lean_ctor_get(v_x_4360_, 0);
lean_inc(v_fst_4363_);
lean_dec_ref(v_x_4360_);
v_fst_4364_ = lean_ctor_get(v_snd_4362_, 0);
lean_inc(v_fst_4364_);
v_snd_4365_ = lean_ctor_get(v_snd_4362_, 1);
lean_inc(v_snd_4365_);
lean_dec(v_snd_4362_);
v___x_4366_ = lean_apply_3(v_h__1_4361_, v_fst_4363_, v_fst_4364_, v_snd_4365_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(lean_object* v_declInfos_4369_, lean_object* v_k_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0));
v___x_4384_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4369_, v_k_4370_, v___x_4383_, v_a_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4385_, lean_object* v_k_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v_a_4395_, lean_object* v_a_4396_, lean_object* v_a_4397_, lean_object* v_a_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(v_declInfos_4385_, v_k_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
lean_dec(v_a_4397_);
lean_dec_ref(v_a_4396_);
lean_dec(v_a_4395_);
lean_dec_ref(v_a_4394_);
lean_dec(v_a_4393_);
lean_dec_ref(v_a_4392_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec_ref(v_a_4387_);
return v_res_4399_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object* v_x_4400_){
_start:
{
uint8_t v___x_4401_; 
v___x_4401_ = 0;
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4402_){
_start:
{
uint8_t v_res_4403_; lean_object* v_r_4404_; 
v_res_4403_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(v_x_4402_);
lean_dec(v_x_4402_);
v_r_4404_ = lean_box(v_res_4403_);
return v_r_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4405_, lean_object* v___x_4406_, uint8_t v___x_4407_, lean_object* v___x_4408_, lean_object* v_fvs_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_){
_start:
{
lean_object* v___x_4417_; 
v___x_4417_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4405_, v___x_4406_, v___x_4407_, v___x_4407_, v___x_4408_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v_a_4418_; uint8_t v___x_4419_; lean_object* v___x_4420_; 
v_a_4418_ = lean_ctor_get(v___x_4417_, 0);
lean_inc(v_a_4418_);
lean_dec_ref_known(v___x_4417_, 1);
v___x_4419_ = 0;
v___x_4420_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4419_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
if (lean_obj_tag(v___x_4420_) == 0)
{
uint8_t v___x_4421_; lean_object* v___x_4422_; 
lean_dec_ref_known(v___x_4420_, 1);
v___x_4421_ = 1;
v___x_4422_ = l_Lean_Meta_mkLetFVars(v_fvs_4409_, v_a_4418_, v___x_4407_, v___x_4407_, v___x_4421_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
return v___x_4422_;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_a_4418_);
v_a_4423_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4420_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4420_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
else
{
return v___x_4417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4431_, lean_object* v___x_4432_, lean_object* v___x_4433_, lean_object* v___x_4434_, lean_object* v_fvs_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
uint8_t v___x_13212__boxed_4443_; lean_object* v_res_4444_; 
v___x_13212__boxed_4443_ = lean_unbox(v___x_4433_);
v_res_4444_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(v_frameStx_4431_, v___x_4432_, v___x_13212__boxed_4443_, v___x_4434_, v_fvs_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_fvs_4435_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object* v_resourceTy_4450_, lean_object* v_frameStx_4451_, lean_object* v___f_4452_, lean_object* v_fvs_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; uint8_t v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___f_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; uint8_t v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4466_, 0, v_resourceTy_4450_);
v___x_4467_ = 1;
v___x_4468_ = lean_box(0);
v___x_4469_ = lean_box(v___x_4467_);
v___f_4470_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed), 12, 5);
lean_closure_set(v___f_4470_, 0, v_frameStx_4451_);
lean_closure_set(v___f_4470_, 1, v___x_4466_);
lean_closure_set(v___f_4470_, 2, v___x_4469_);
lean_closure_set(v___f_4470_, 3, v___x_4468_);
lean_closure_set(v___f_4470_, 4, v_fvs_4453_);
v___x_4471_ = lean_box(0);
v___x_4472_ = lean_box(1);
v___x_4473_ = 0;
v___x_4474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0));
v___x_4475_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4475_, 0, v___x_4468_);
lean_ctor_set(v___x_4475_, 1, v___x_4471_);
lean_ctor_set(v___x_4475_, 2, v___x_4468_);
lean_ctor_set(v___x_4475_, 3, v___f_4452_);
lean_ctor_set(v___x_4475_, 4, v___x_4472_);
lean_ctor_set(v___x_4475_, 5, v___x_4472_);
lean_ctor_set(v___x_4475_, 6, v___x_4468_);
lean_ctor_set(v___x_4475_, 7, v___x_4474_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8, v___x_4467_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 1, v___x_4467_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 2, v___x_4467_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 3, v___x_4467_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 4, v___x_4473_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 5, v___x_4473_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 6, v___x_4473_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 7, v___x_4473_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 8, v___x_4467_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 9, v___x_4473_);
lean_ctor_set_uint8(v___x_4475_, sizeof(void*)*8 + 10, v___x_4467_);
v___x_4476_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1));
v___x_4477_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4470_, v___x_4475_, v___x_4476_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v_fst_4479_; lean_object* v___x_4480_; 
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4477_, 1);
v_fst_4479_ = lean_ctor_get(v_a_4478_, 0);
lean_inc(v_fst_4479_);
lean_dec(v_a_4478_);
v___x_4480_ = l_Lean_Meta_Sym_instantiateMVarsS(v_fst_4479_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
return v___x_4480_;
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
v_a_4481_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4477_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4477_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object* v_resourceTy_4489_, lean_object* v_frameStx_4490_, lean_object* v___f_4491_, lean_object* v_fvs_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(v_resourceTy_4489_, v_frameStx_4490_, v___f_4491_, v_fvs_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object* v___x_4506_, lean_object* v_res_4507_, lean_object* v_range_4508_, lean_object* v_b_4509_, lean_object* v_i_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v_stop_4516_; lean_object* v_step_4517_; lean_object* v_a_4519_; uint8_t v___x_4522_; 
v_stop_4516_ = lean_ctor_get(v_range_4508_, 1);
v_step_4517_ = lean_ctor_get(v_range_4508_, 2);
v___x_4522_ = lean_nat_dec_lt(v_i_4510_, v_stop_4516_);
if (v___x_4522_ == 0)
{
lean_object* v___x_4523_; 
lean_dec(v_i_4510_);
v___x_4523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4523_, 0, v_b_4509_);
return v___x_4523_;
}
else
{
lean_object* v___x_4524_; 
v___x_4524_ = lean_array_fget_borrowed(v___x_4506_, v_i_4510_);
if (lean_obj_tag(v___x_4524_) == 1)
{
lean_object* v_val_4525_; lean_object* v_args_4526_; lean_object* v___x_4527_; uint8_t v___x_4528_; 
v_val_4525_ = lean_ctor_get(v___x_4524_, 0);
v_args_4526_ = lean_ctor_get(v_res_4507_, 1);
v___x_4527_ = lean_array_get_size(v_args_4526_);
v___x_4528_ = lean_nat_dec_lt(v_i_4510_, v___x_4527_);
if (v___x_4528_ == 0)
{
v_a_4519_ = v_b_4509_;
goto v___jp_4518_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v___x_4529_ = l_Lean_instInhabitedExpr;
v___x_4530_ = lean_array_get_borrowed(v___x_4529_, v_args_4526_, v_i_4510_);
lean_inc(v___y_4514_);
lean_inc_ref(v___y_4513_);
lean_inc(v___y_4512_);
lean_inc_ref(v___y_4511_);
lean_inc(v___x_4530_);
v___x_4531_ = lean_infer_type(v___x_4530_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
lean_inc(v___x_4530_);
v___x_4533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4533_, 0, v_a_4532_);
lean_ctor_set(v___x_4533_, 1, v___x_4530_);
lean_inc(v_val_4525_);
v___x_4534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4534_, 0, v_val_4525_);
lean_ctor_set(v___x_4534_, 1, v___x_4533_);
v___x_4535_ = lean_array_push(v_b_4509_, v___x_4534_);
v_a_4519_ = v___x_4535_;
goto v___jp_4518_;
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v_i_4510_);
lean_dec_ref(v_b_4509_);
v_a_4536_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4531_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4531_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
else
{
v_a_4519_ = v_b_4509_;
goto v___jp_4518_;
}
}
v___jp_4518_:
{
lean_object* v___x_4520_; 
v___x_4520_ = lean_nat_add(v_i_4510_, v_step_4517_);
lean_dec(v_i_4510_);
v_b_4509_ = v_a_4519_;
v_i_4510_ = v___x_4520_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v___x_4544_, lean_object* v_res_4545_, lean_object* v_range_4546_, lean_object* v_b_4547_, lean_object* v_i_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v___x_4544_, v_res_4545_, v_range_4546_, v_b_4547_, v_i_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec_ref(v_range_4546_);
lean_dec_ref(v_res_4545_);
lean_dec_ref(v___x_4544_);
return v_res_4554_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2(void){
_start:
{
uint8_t v___x_4558_; uint64_t v___x_4559_; 
v___x_4558_ = 1;
v___x_4559_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4558_);
return v___x_4559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object* v_resourceTy_4560_, lean_object* v_entry_4561_, lean_object* v_res_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_){
_start:
{
lean_object* v_varNames_4575_; lean_object* v_frameStx_4576_; lean_object* v___x_4577_; lean_object* v_decls_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; 
v_varNames_4575_ = lean_ctor_get(v_entry_4561_, 1);
lean_inc_ref(v_varNames_4575_);
v_frameStx_4576_ = lean_ctor_get(v_entry_4561_, 2);
lean_inc(v_frameStx_4576_);
lean_dec_ref(v_entry_4561_);
v___x_4577_ = lean_unsigned_to_nat(0u);
v_decls_4578_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0));
v___x_4579_ = lean_array_get_size(v_varNames_4575_);
v___x_4580_ = lean_unsigned_to_nat(1u);
v___x_4581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4577_);
lean_ctor_set(v___x_4581_, 1, v___x_4579_);
lean_ctor_set(v___x_4581_, 2, v___x_4580_);
v___x_4582_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_varNames_4575_, v_res_4562_, v___x_4581_, v_decls_4578_, v___x_4577_, v_a_4570_, v_a_4571_, v_a_4572_, v_a_4573_);
lean_dec_ref_known(v___x_4581_, 3);
lean_dec_ref(v_varNames_4575_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4584_; uint8_t v_foApprox_4585_; uint8_t v_ctxApprox_4586_; uint8_t v_quasiPatternApprox_4587_; uint8_t v_constApprox_4588_; uint8_t v_isDefEqStuckEx_4589_; uint8_t v_unificationHints_4590_; uint8_t v_proofIrrelevance_4591_; uint8_t v_assignSyntheticOpaque_4592_; uint8_t v_offsetCnstrs_4593_; uint8_t v_etaStruct_4594_; uint8_t v_univApprox_4595_; uint8_t v_iota_4596_; uint8_t v_beta_4597_; uint8_t v_proj_4598_; uint8_t v_zeta_4599_; uint8_t v_zetaDelta_4600_; uint8_t v_zetaUnused_4601_; uint8_t v_zetaHave_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4639_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v___x_4582_, 1);
v___x_4584_ = l_Lean_Meta_Context_config(v_a_4570_);
v_foApprox_4585_ = lean_ctor_get_uint8(v___x_4584_, 0);
v_ctxApprox_4586_ = lean_ctor_get_uint8(v___x_4584_, 1);
v_quasiPatternApprox_4587_ = lean_ctor_get_uint8(v___x_4584_, 2);
v_constApprox_4588_ = lean_ctor_get_uint8(v___x_4584_, 3);
v_isDefEqStuckEx_4589_ = lean_ctor_get_uint8(v___x_4584_, 4);
v_unificationHints_4590_ = lean_ctor_get_uint8(v___x_4584_, 5);
v_proofIrrelevance_4591_ = lean_ctor_get_uint8(v___x_4584_, 6);
v_assignSyntheticOpaque_4592_ = lean_ctor_get_uint8(v___x_4584_, 7);
v_offsetCnstrs_4593_ = lean_ctor_get_uint8(v___x_4584_, 8);
v_etaStruct_4594_ = lean_ctor_get_uint8(v___x_4584_, 10);
v_univApprox_4595_ = lean_ctor_get_uint8(v___x_4584_, 11);
v_iota_4596_ = lean_ctor_get_uint8(v___x_4584_, 12);
v_beta_4597_ = lean_ctor_get_uint8(v___x_4584_, 13);
v_proj_4598_ = lean_ctor_get_uint8(v___x_4584_, 14);
v_zeta_4599_ = lean_ctor_get_uint8(v___x_4584_, 15);
v_zetaDelta_4600_ = lean_ctor_get_uint8(v___x_4584_, 16);
v_zetaUnused_4601_ = lean_ctor_get_uint8(v___x_4584_, 17);
v_zetaHave_4602_ = lean_ctor_get_uint8(v___x_4584_, 18);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4604_ = v___x_4584_;
v_isShared_4605_ = v_isSharedCheck_4639_;
goto v_resetjp_4603_;
}
else
{
lean_dec(v___x_4584_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4639_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
uint8_t v_trackZetaDelta_4606_; lean_object* v_zetaDeltaSet_4607_; lean_object* v_lctx_4608_; lean_object* v_localInstances_4609_; lean_object* v_defEqCtx_x3f_4610_; lean_object* v_synthPendingDepth_4611_; lean_object* v_canUnfold_x3f_4612_; uint8_t v_univApprox_4613_; uint8_t v_inTypeClassResolution_4614_; uint8_t v_cacheInferType_4615_; uint8_t v___x_4616_; lean_object* v_config_4618_; 
v_trackZetaDelta_4606_ = lean_ctor_get_uint8(v_a_4570_, sizeof(void*)*7);
v_zetaDeltaSet_4607_ = lean_ctor_get(v_a_4570_, 1);
v_lctx_4608_ = lean_ctor_get(v_a_4570_, 2);
v_localInstances_4609_ = lean_ctor_get(v_a_4570_, 3);
v_defEqCtx_x3f_4610_ = lean_ctor_get(v_a_4570_, 4);
v_synthPendingDepth_4611_ = lean_ctor_get(v_a_4570_, 5);
v_canUnfold_x3f_4612_ = lean_ctor_get(v_a_4570_, 6);
v_univApprox_4613_ = lean_ctor_get_uint8(v_a_4570_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4614_ = lean_ctor_get_uint8(v_a_4570_, sizeof(void*)*7 + 2);
v_cacheInferType_4615_ = lean_ctor_get_uint8(v_a_4570_, sizeof(void*)*7 + 3);
v___x_4616_ = 1;
if (v_isShared_4605_ == 0)
{
v_config_4618_ = v___x_4604_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 0, v_foApprox_4585_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 1, v_ctxApprox_4586_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 2, v_quasiPatternApprox_4587_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 3, v_constApprox_4588_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 4, v_isDefEqStuckEx_4589_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 5, v_unificationHints_4590_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 6, v_proofIrrelevance_4591_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 7, v_assignSyntheticOpaque_4592_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 8, v_offsetCnstrs_4593_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 10, v_etaStruct_4594_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 11, v_univApprox_4595_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 12, v_iota_4596_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 13, v_beta_4597_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 14, v_proj_4598_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 15, v_zeta_4599_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 16, v_zetaDelta_4600_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 17, v_zetaUnused_4601_);
lean_ctor_set_uint8(v_reuseFailAlloc_4638_, 18, v_zetaHave_4602_);
v_config_4618_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
uint64_t v___x_4619_; uint64_t v___x_4620_; uint64_t v___x_4621_; lean_object* v___f_4622_; lean_object* v___f_4623_; uint64_t v___x_4624_; uint64_t v___x_4625_; uint64_t v_key_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; 
lean_ctor_set_uint8(v_config_4618_, 9, v___x_4616_);
v___x_4619_ = l_Lean_Meta_Context_configKey(v_a_4570_);
v___x_4620_ = 3ULL;
v___x_4621_ = lean_uint64_shift_right(v___x_4619_, v___x_4620_);
v___f_4622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1));
v___f_4623_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4623_, 0, v_resourceTy_4560_);
lean_closure_set(v___f_4623_, 1, v_frameStx_4576_);
lean_closure_set(v___f_4623_, 2, v___f_4622_);
v___x_4624_ = lean_uint64_shift_left(v___x_4621_, v___x_4620_);
v___x_4625_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2);
v_key_4626_ = lean_uint64_lor(v___x_4624_, v___x_4625_);
v___x_4627_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4627_, 0, v_config_4618_);
lean_ctor_set_uint64(v___x_4627_, sizeof(void*)*1, v_key_4626_);
lean_inc(v_canUnfold_x3f_4612_);
lean_inc(v_synthPendingDepth_4611_);
lean_inc(v_defEqCtx_x3f_4610_);
lean_inc_ref(v_localInstances_4609_);
lean_inc_ref(v_lctx_4608_);
lean_inc(v_zetaDeltaSet_4607_);
v___x_4628_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4628_, 0, v___x_4627_);
lean_ctor_set(v___x_4628_, 1, v_zetaDeltaSet_4607_);
lean_ctor_set(v___x_4628_, 2, v_lctx_4608_);
lean_ctor_set(v___x_4628_, 3, v_localInstances_4609_);
lean_ctor_set(v___x_4628_, 4, v_defEqCtx_x3f_4610_);
lean_ctor_set(v___x_4628_, 5, v_synthPendingDepth_4611_);
lean_ctor_set(v___x_4628_, 6, v_canUnfold_x3f_4612_);
lean_ctor_set_uint8(v___x_4628_, sizeof(void*)*7, v_trackZetaDelta_4606_);
lean_ctor_set_uint8(v___x_4628_, sizeof(void*)*7 + 1, v_univApprox_4613_);
lean_ctor_set_uint8(v___x_4628_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4614_);
lean_ctor_set_uint8(v___x_4628_, sizeof(void*)*7 + 3, v_cacheInferType_4615_);
v___x_4629_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_a_4583_, v___f_4623_, v_decls_4578_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_, v___x_4628_, v_a_4571_, v_a_4572_, v_a_4573_);
lean_dec_ref_known(v___x_4628_, 7);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4629_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4629_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4629_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
else
{
return v___x_4629_;
}
}
}
}
else
{
lean_object* v_a_4640_; lean_object* v___x_4642_; uint8_t v_isShared_4643_; uint8_t v_isSharedCheck_4647_; 
lean_dec(v_frameStx_4576_);
lean_dec_ref(v_resourceTy_4560_);
v_a_4640_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4647_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4647_ == 0)
{
v___x_4642_ = v___x_4582_;
v_isShared_4643_ = v_isSharedCheck_4647_;
goto v_resetjp_4641_;
}
else
{
lean_inc(v_a_4640_);
lean_dec(v___x_4582_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object* v_resourceTy_4648_, lean_object* v_entry_4649_, lean_object* v_res_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_, lean_object* v_a_4653_, lean_object* v_a_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_, lean_object* v_a_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_resourceTy_4648_, v_entry_4649_, v_res_4650_, v_a_4651_, v_a_4652_, v_a_4653_, v_a_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_);
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
lean_dec_ref(v_res_4650_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object* v___x_4664_, lean_object* v_res_4665_, lean_object* v_range_4666_, lean_object* v_b_4667_, lean_object* v_i_4668_, lean_object* v_hs_4669_, lean_object* v_hl_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v___x_4683_; 
v___x_4683_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v___x_4664_, v_res_4665_, v_range_4666_, v_b_4667_, v_i_4668_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
return v___x_4683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object** _args){
lean_object* v___x_4684_ = _args[0];
lean_object* v_res_4685_ = _args[1];
lean_object* v_range_4686_ = _args[2];
lean_object* v_b_4687_ = _args[3];
lean_object* v_i_4688_ = _args[4];
lean_object* v_hs_4689_ = _args[5];
lean_object* v_hl_4690_ = _args[6];
lean_object* v___y_4691_ = _args[7];
lean_object* v___y_4692_ = _args[8];
lean_object* v___y_4693_ = _args[9];
lean_object* v___y_4694_ = _args[10];
lean_object* v___y_4695_ = _args[11];
lean_object* v___y_4696_ = _args[12];
lean_object* v___y_4697_ = _args[13];
lean_object* v___y_4698_ = _args[14];
lean_object* v___y_4699_ = _args[15];
lean_object* v___y_4700_ = _args[16];
lean_object* v___y_4701_ = _args[17];
lean_object* v___y_4702_ = _args[18];
_start:
{
lean_object* v_res_4703_; 
v_res_4703_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(v___x_4684_, v_res_4685_, v_range_4686_, v_b_4687_, v_i_4688_, v_hs_4689_, v_hl_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
lean_dec_ref(v___y_4694_);
lean_dec(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec_ref(v_range_4686_);
lean_dec_ref(v_res_4685_);
lean_dec_ref(v___x_4684_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v___x_4704_, lean_object* v___x_4705_, lean_object* v_as_4706_, size_t v_sz_4707_, size_t v_i_4708_, lean_object* v_b_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v_a_4718_; uint8_t v___x_4722_; 
v___x_4722_ = lean_usize_dec_lt(v_i_4708_, v_sz_4707_);
if (v___x_4722_ == 0)
{
lean_object* v___x_4723_; 
lean_dec_ref(v___x_4705_);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v_b_4709_);
return v___x_4723_;
}
else
{
lean_object* v_entries_4724_; lean_object* v___x_4725_; lean_object* v_a_4726_; lean_object* v___x_4727_; uint8_t v_retired_4728_; 
v_entries_4724_ = lean_ctor_get(v___x_4704_, 1);
v___x_4725_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
v_a_4726_ = lean_array_uget_borrowed(v_as_4706_, v_i_4708_);
v___x_4727_ = lean_array_get_borrowed(v___x_4725_, v_entries_4724_, v_a_4726_);
v_retired_4728_ = lean_ctor_get_uint8(v___x_4727_, sizeof(void*)*4);
if (v_retired_4728_ == 0)
{
lean_object* v_pat_4729_; lean_object* v_srcIdx_4730_; lean_object* v___x_4731_; 
v_pat_4729_ = lean_ctor_get(v___x_4727_, 0);
v_srcIdx_4730_ = lean_ctor_get(v___x_4727_, 3);
lean_inc_ref(v___x_4705_);
lean_inc_ref(v_pat_4729_);
v___x_4731_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4729_, v___x_4705_, v___x_4722_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
lean_inc(v_a_4732_);
lean_dec_ref_known(v___x_4731_, 1);
if (lean_obj_tag(v_a_4732_) == 1)
{
if (lean_obj_tag(v_b_4709_) == 0)
{
lean_object* v_val_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4741_; 
v_val_4733_ = lean_ctor_get(v_a_4732_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v_a_4732_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4735_ = v_a_4732_;
v_isShared_4736_ = v_isSharedCheck_4741_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_val_4733_);
lean_dec(v_a_4732_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4741_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4737_; lean_object* v___x_4739_; 
lean_inc(v___x_4727_);
v___x_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4727_);
lean_ctor_set(v___x_4737_, 1, v_val_4733_);
if (v_isShared_4736_ == 0)
{
lean_ctor_set(v___x_4735_, 0, v___x_4737_);
v___x_4739_ = v___x_4735_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v___x_4737_);
v___x_4739_ = v_reuseFailAlloc_4740_;
goto v_reusejp_4738_;
}
v_reusejp_4738_:
{
v_a_4718_ = v___x_4739_;
goto v___jp_4717_;
}
}
}
else
{
lean_object* v_val_4742_; lean_object* v_fst_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4761_; 
v_val_4742_ = lean_ctor_get(v_b_4709_, 0);
lean_inc(v_val_4742_);
v_fst_4743_ = lean_ctor_get(v_val_4742_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v_val_4742_);
if (v_isSharedCheck_4761_ == 0)
{
lean_object* v_unused_4762_; 
v_unused_4762_ = lean_ctor_get(v_val_4742_, 1);
lean_dec(v_unused_4762_);
v___x_4745_ = v_val_4742_;
v_isShared_4746_ = v_isSharedCheck_4761_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_fst_4743_);
lean_dec(v_val_4742_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4761_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v_val_4747_; lean_object* v_srcIdx_4748_; uint8_t v___x_4749_; 
v_val_4747_ = lean_ctor_get(v_a_4732_, 0);
lean_inc(v_val_4747_);
lean_dec_ref_known(v_a_4732_, 1);
v_srcIdx_4748_ = lean_ctor_get(v_fst_4743_, 3);
lean_inc(v_srcIdx_4748_);
lean_dec(v_fst_4743_);
v___x_4749_ = lean_nat_dec_lt(v_srcIdx_4730_, v_srcIdx_4748_);
lean_dec(v_srcIdx_4748_);
if (v___x_4749_ == 0)
{
lean_dec(v_val_4747_);
lean_del_object(v___x_4745_);
v_a_4718_ = v_b_4709_;
goto v___jp_4717_;
}
else
{
lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4759_; 
v_isSharedCheck_4759_ = !lean_is_exclusive(v_b_4709_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v_b_4709_, 0);
lean_dec(v_unused_4760_);
v___x_4751_ = v_b_4709_;
v_isShared_4752_ = v_isSharedCheck_4759_;
goto v_resetjp_4750_;
}
else
{
lean_dec(v_b_4709_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4759_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
lean_inc(v___x_4727_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 1, v_val_4747_);
lean_ctor_set(v___x_4745_, 0, v___x_4727_);
v___x_4754_ = v___x_4745_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4727_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_val_4747_);
v___x_4754_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
lean_object* v___x_4756_; 
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 0, v___x_4754_);
v___x_4756_ = v___x_4751_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
v_a_4718_ = v___x_4756_;
goto v___jp_4717_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4732_);
v_a_4718_ = v_b_4709_;
goto v___jp_4717_;
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec(v_b_4709_);
lean_dec_ref(v___x_4705_);
v_a_4763_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4731_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4731_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
else
{
v_a_4718_ = v_b_4709_;
goto v___jp_4717_;
}
}
v___jp_4717_:
{
size_t v___x_4719_; size_t v___x_4720_; 
v___x_4719_ = ((size_t)1ULL);
v___x_4720_ = lean_usize_add(v_i_4708_, v___x_4719_);
v_i_4708_ = v___x_4720_;
v_b_4709_ = v_a_4718_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v___x_4771_, lean_object* v___x_4772_, lean_object* v_as_4773_, lean_object* v_sz_4774_, lean_object* v_i_4775_, lean_object* v_b_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
size_t v_sz_boxed_4784_; size_t v_i_boxed_4785_; lean_object* v_res_4786_; 
v_sz_boxed_4784_ = lean_unbox_usize(v_sz_4774_);
lean_dec(v_sz_4774_);
v_i_boxed_4785_ = lean_unbox_usize(v_i_4775_);
lean_dec(v_i_4775_);
v_res_4786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4771_, v___x_4772_, v_as_4773_, v_sz_boxed_4784_, v_i_boxed_4785_, v_b_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec_ref(v_as_4773_);
lean_dec_ref(v___x_4771_);
return v_res_4786_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1(void){
_start:
{
lean_object* v___x_4788_; lean_object* v___x_4789_; 
v___x_4788_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0));
v___x_4789_ = l_Lean_stringToMessageData(v___x_4788_);
return v___x_4789_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3(void){
_start:
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2));
v___x_4792_ = l_Lean_stringToMessageData(v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object* v_resourceTy_4793_, lean_object* v_info_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v___x_4807_; lean_object* v_frameDB_4808_; lean_object* v_tree_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; size_t v_sz_4813_; size_t v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4817_; uint8_t v_isShared_4818_; uint8_t v_isSharedCheck_4928_; 
v___x_4807_ = lean_st_ref_get(v_a_4796_);
v_frameDB_4808_ = lean_ctor_get(v___x_4807_, 4);
lean_inc_ref(v_frameDB_4808_);
lean_dec(v___x_4807_);
v_tree_4809_ = lean_ctor_get(v_frameDB_4808_, 0);
v___x_4810_ = lean_box(0);
v___x_4811_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_4794_);
v___x_4812_ = l_Lean_Meta_Sym_getMatch___redArg(v_tree_4809_, v___x_4811_);
v_sz_4813_ = lean_array_size(v___x_4812_);
v___x_4814_ = ((size_t)0ULL);
lean_inc_ref(v___x_4811_);
v___x_4815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_frameDB_4808_, v___x_4811_, v___x_4812_, v_sz_4813_, v___x_4814_, v___x_4810_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
lean_dec_ref(v___x_4812_);
v_isSharedCheck_4928_ = !lean_is_exclusive(v_frameDB_4808_);
if (v_isSharedCheck_4928_ == 0)
{
lean_object* v_unused_4929_; lean_object* v_unused_4930_; 
v_unused_4929_ = lean_ctor_get(v_frameDB_4808_, 1);
lean_dec(v_unused_4929_);
v_unused_4930_ = lean_ctor_get(v_frameDB_4808_, 0);
lean_dec(v_unused_4930_);
v___x_4817_ = v_frameDB_4808_;
v_isShared_4818_ = v_isSharedCheck_4928_;
goto v_resetjp_4816_;
}
else
{
lean_dec(v_frameDB_4808_);
v___x_4817_ = lean_box(0);
v_isShared_4818_ = v_isSharedCheck_4928_;
goto v_resetjp_4816_;
}
v_resetjp_4816_:
{
if (lean_obj_tag(v___x_4815_) == 0)
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4919_; 
v_a_4819_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4919_ == 0)
{
v___x_4821_ = v___x_4815_;
v_isShared_4822_ = v_isSharedCheck_4919_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4815_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4919_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
if (lean_obj_tag(v_a_4819_) == 1)
{
lean_object* v_val_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4915_; 
lean_del_object(v___x_4821_);
v_val_4823_ = lean_ctor_get(v_a_4819_, 0);
v_isSharedCheck_4915_ = !lean_is_exclusive(v_a_4819_);
if (v_isSharedCheck_4915_ == 0)
{
v___x_4825_ = v_a_4819_;
v_isShared_4826_ = v_isSharedCheck_4915_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_val_4823_);
lean_dec(v_a_4819_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4915_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v_fst_4827_; lean_object* v_snd_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4914_; 
v_fst_4827_ = lean_ctor_get(v_val_4823_, 0);
v_snd_4828_ = lean_ctor_get(v_val_4823_, 1);
v_isSharedCheck_4914_ = !lean_is_exclusive(v_val_4823_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4830_ = v_val_4823_;
v_isShared_4831_ = v_isSharedCheck_4914_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_snd_4828_);
lean_inc(v_fst_4827_);
lean_dec(v_val_4823_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4914_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4832_; lean_object* v_frameDB_4833_; lean_object* v_specBackwardRuleCache_4834_; lean_object* v_splitBackwardRuleCache_4835_; lean_object* v_latticeBackwardRuleCache_4836_; lean_object* v_frameBackwardRuleCache_4837_; lean_object* v_invariants_4838_; lean_object* v_vcs_4839_; lean_object* v_simpState_4840_; lean_object* v_fuel_4841_; lean_object* v_inlineHandledInvariants_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4913_; 
v___x_4832_ = lean_st_ref_take(v_a_4796_);
v_frameDB_4833_ = lean_ctor_get(v___x_4832_, 4);
v_specBackwardRuleCache_4834_ = lean_ctor_get(v___x_4832_, 0);
v_splitBackwardRuleCache_4835_ = lean_ctor_get(v___x_4832_, 1);
v_latticeBackwardRuleCache_4836_ = lean_ctor_get(v___x_4832_, 2);
v_frameBackwardRuleCache_4837_ = lean_ctor_get(v___x_4832_, 3);
v_invariants_4838_ = lean_ctor_get(v___x_4832_, 5);
v_vcs_4839_ = lean_ctor_get(v___x_4832_, 6);
v_simpState_4840_ = lean_ctor_get(v___x_4832_, 7);
v_fuel_4841_ = lean_ctor_get(v___x_4832_, 8);
v_inlineHandledInvariants_4842_ = lean_ctor_get(v___x_4832_, 9);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4832_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4844_ = v___x_4832_;
v_isShared_4845_ = v_isSharedCheck_4913_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_inlineHandledInvariants_4842_);
lean_inc(v_fuel_4841_);
lean_inc(v_simpState_4840_);
lean_inc(v_vcs_4839_);
lean_inc(v_invariants_4838_);
lean_inc(v_frameDB_4833_);
lean_inc(v_frameBackwardRuleCache_4837_);
lean_inc(v_latticeBackwardRuleCache_4836_);
lean_inc(v_splitBackwardRuleCache_4835_);
lean_inc(v_specBackwardRuleCache_4834_);
lean_dec(v___x_4832_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4913_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
lean_object* v_tree_4846_; lean_object* v_entries_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4912_; 
v_tree_4846_ = lean_ctor_get(v_frameDB_4833_, 0);
v_entries_4847_ = lean_ctor_get(v_frameDB_4833_, 1);
v_isSharedCheck_4912_ = !lean_is_exclusive(v_frameDB_4833_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4849_ = v_frameDB_4833_;
v_isShared_4850_ = v_isSharedCheck_4912_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_entries_4847_);
lean_inc(v_tree_4846_);
lean_dec(v_frameDB_4833_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4912_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v_pat_4851_; lean_object* v_varNames_4852_; lean_object* v_frameStx_4853_; lean_object* v_srcIdx_4854_; uint8_t v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4859_; 
v_pat_4851_ = lean_ctor_get(v_fst_4827_, 0);
v_varNames_4852_ = lean_ctor_get(v_fst_4827_, 1);
v_frameStx_4853_ = lean_ctor_get(v_fst_4827_, 2);
v_srcIdx_4854_ = lean_ctor_get(v_fst_4827_, 3);
v___x_4855_ = 1;
lean_inc(v_srcIdx_4854_);
lean_inc(v_frameStx_4853_);
lean_inc_ref(v_varNames_4852_);
lean_inc_ref(v_pat_4851_);
v___x_4856_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_4856_, 0, v_pat_4851_);
lean_ctor_set(v___x_4856_, 1, v_varNames_4852_);
lean_ctor_set(v___x_4856_, 2, v_frameStx_4853_);
lean_ctor_set(v___x_4856_, 3, v_srcIdx_4854_);
lean_ctor_set_uint8(v___x_4856_, sizeof(void*)*4, v___x_4855_);
v___x_4857_ = lean_array_set(v_entries_4847_, v_srcIdx_4854_, v___x_4856_);
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 1, v___x_4857_);
v___x_4859_ = v___x_4849_;
goto v_reusejp_4858_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_tree_4846_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v___x_4857_);
v___x_4859_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4858_;
}
v_reusejp_4858_:
{
lean_object* v___x_4861_; 
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 4, v___x_4859_);
v___x_4861_ = v___x_4844_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4910_; 
v_reuseFailAlloc_4910_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4910_, 0, v_specBackwardRuleCache_4834_);
lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_splitBackwardRuleCache_4835_);
lean_ctor_set(v_reuseFailAlloc_4910_, 2, v_latticeBackwardRuleCache_4836_);
lean_ctor_set(v_reuseFailAlloc_4910_, 3, v_frameBackwardRuleCache_4837_);
lean_ctor_set(v_reuseFailAlloc_4910_, 4, v___x_4859_);
lean_ctor_set(v_reuseFailAlloc_4910_, 5, v_invariants_4838_);
lean_ctor_set(v_reuseFailAlloc_4910_, 6, v_vcs_4839_);
lean_ctor_set(v_reuseFailAlloc_4910_, 7, v_simpState_4840_);
lean_ctor_set(v_reuseFailAlloc_4910_, 8, v_fuel_4841_);
lean_ctor_set(v_reuseFailAlloc_4910_, 9, v_inlineHandledInvariants_4842_);
v___x_4861_ = v_reuseFailAlloc_4910_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
lean_object* v___x_4862_; lean_object* v___x_4863_; 
v___x_4862_ = lean_st_ref_set(v_a_4796_, v___x_4861_);
v___x_4863_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_resourceTy_4793_, v_fst_4827_, v_snd_4828_, v_a_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
lean_dec(v_snd_4828_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4901_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4901_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4901_ == 0)
{
v___x_4866_ = v___x_4863_;
v_isShared_4867_ = v_isSharedCheck_4901_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4863_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4901_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v_options_4875_; uint8_t v_hasTrace_4876_; 
v_options_4875_ = lean_ctor_get(v_a_4804_, 2);
v_hasTrace_4876_ = lean_ctor_get_uint8(v_options_4875_, sizeof(void*)*1);
if (v_hasTrace_4876_ == 0)
{
lean_del_object(v___x_4830_);
lean_del_object(v___x_4817_);
lean_dec_ref(v___x_4811_);
goto v___jp_4868_;
}
else
{
lean_object* v_inheritedTraceOptions_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; uint8_t v___x_4880_; 
v_inheritedTraceOptions_4877_ = lean_ctor_get(v_a_4804_, 13);
v___x_4878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4879_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4880_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4877_, v_options_4875_, v___x_4879_);
if (v___x_4880_ == 0)
{
lean_del_object(v___x_4830_);
lean_del_object(v___x_4817_);
lean_dec_ref(v___x_4811_);
goto v___jp_4868_;
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4884_; 
v___x_4881_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1);
v___x_4882_ = l_Lean_MessageData_ofExpr(v___x_4811_);
if (v_isShared_4831_ == 0)
{
lean_ctor_set_tag(v___x_4830_, 7);
lean_ctor_set(v___x_4830_, 1, v___x_4882_);
lean_ctor_set(v___x_4830_, 0, v___x_4881_);
v___x_4884_ = v___x_4830_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4881_);
lean_ctor_set(v_reuseFailAlloc_4900_, 1, v___x_4882_);
v___x_4884_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4885_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3);
if (v_isShared_4818_ == 0)
{
lean_ctor_set_tag(v___x_4817_, 7);
lean_ctor_set(v___x_4817_, 1, v___x_4885_);
lean_ctor_set(v___x_4817_, 0, v___x_4884_);
v___x_4887_ = v___x_4817_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v___x_4884_);
lean_ctor_set(v_reuseFailAlloc_4899_, 1, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
lean_inc(v_a_4864_);
v___x_4888_ = l_Lean_indentExpr(v_a_4864_);
v___x_4889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4887_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4878_, v___x_4889_, v_a_4802_, v_a_4803_, v_a_4804_, v_a_4805_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_dec_ref_known(v___x_4890_, 1);
goto v___jp_4868_;
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_del_object(v___x_4866_);
lean_dec(v_a_4864_);
lean_del_object(v___x_4825_);
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4890_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4890_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
}
}
v___jp_4868_:
{
lean_object* v___x_4870_; 
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 0, v_a_4864_);
v___x_4870_ = v___x_4825_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4864_);
v___x_4870_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
lean_object* v___x_4872_; 
if (v_isShared_4867_ == 0)
{
lean_ctor_set(v___x_4866_, 0, v___x_4870_);
v___x_4872_ = v___x_4866_;
goto v_reusejp_4871_;
}
else
{
lean_object* v_reuseFailAlloc_4873_; 
v_reuseFailAlloc_4873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4870_);
v___x_4872_ = v_reuseFailAlloc_4873_;
goto v_reusejp_4871_;
}
v_reusejp_4871_:
{
return v___x_4872_;
}
}
}
}
}
else
{
lean_object* v_a_4902_; lean_object* v___x_4904_; uint8_t v_isShared_4905_; uint8_t v_isSharedCheck_4909_; 
lean_del_object(v___x_4830_);
lean_del_object(v___x_4825_);
lean_del_object(v___x_4817_);
lean_dec_ref(v___x_4811_);
v_a_4902_ = lean_ctor_get(v___x_4863_, 0);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4863_);
if (v_isSharedCheck_4909_ == 0)
{
v___x_4904_ = v___x_4863_;
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
else
{
lean_inc(v_a_4902_);
lean_dec(v___x_4863_);
v___x_4904_ = lean_box(0);
v_isShared_4905_ = v_isSharedCheck_4909_;
goto v_resetjp_4903_;
}
v_resetjp_4903_:
{
lean_object* v___x_4907_; 
if (v_isShared_4905_ == 0)
{
v___x_4907_ = v___x_4904_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_a_4902_);
v___x_4907_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
return v___x_4907_;
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
lean_object* v___x_4917_; 
lean_dec(v_a_4819_);
lean_del_object(v___x_4817_);
lean_dec_ref(v___x_4811_);
lean_dec_ref(v_resourceTy_4793_);
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v___x_4810_);
v___x_4917_ = v___x_4821_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4810_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
lean_del_object(v___x_4817_);
lean_dec_ref(v___x_4811_);
lean_dec_ref(v_resourceTy_4793_);
v_a_4920_ = lean_ctor_get(v___x_4815_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4815_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4815_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4815_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object* v_resourceTy_4931_, lean_object* v_info_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_, lean_object* v_a_4935_, lean_object* v_a_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v_a_4939_, lean_object* v_a_4940_, lean_object* v_a_4941_, lean_object* v_a_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_){
_start:
{
lean_object* v_res_4945_; 
v_res_4945_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_resourceTy_4931_, v_info_4932_, v_a_4933_, v_a_4934_, v_a_4935_, v_a_4936_, v_a_4937_, v_a_4938_, v_a_4939_, v_a_4940_, v_a_4941_, v_a_4942_, v_a_4943_);
lean_dec(v_a_4943_);
lean_dec_ref(v_a_4942_);
lean_dec(v_a_4941_);
lean_dec_ref(v_a_4940_);
lean_dec(v_a_4939_);
lean_dec_ref(v_a_4938_);
lean_dec(v_a_4937_);
lean_dec_ref(v_a_4936_);
lean_dec(v_a_4935_);
lean_dec(v_a_4934_);
lean_dec_ref(v_a_4933_);
lean_dec_ref(v_info_4932_);
return v_res_4945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object* v___x_4946_, lean_object* v___x_4947_, lean_object* v_as_4948_, size_t v_sz_4949_, size_t v_i_4950_, lean_object* v_b_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v___x_4946_, v___x_4947_, v_as_4948_, v_sz_4949_, v_i_4950_, v_b_4951_, v___y_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v___x_4965_ = _args[0];
lean_object* v___x_4966_ = _args[1];
lean_object* v_as_4967_ = _args[2];
lean_object* v_sz_4968_ = _args[3];
lean_object* v_i_4969_ = _args[4];
lean_object* v_b_4970_ = _args[5];
lean_object* v___y_4971_ = _args[6];
lean_object* v___y_4972_ = _args[7];
lean_object* v___y_4973_ = _args[8];
lean_object* v___y_4974_ = _args[9];
lean_object* v___y_4975_ = _args[10];
lean_object* v___y_4976_ = _args[11];
lean_object* v___y_4977_ = _args[12];
lean_object* v___y_4978_ = _args[13];
lean_object* v___y_4979_ = _args[14];
lean_object* v___y_4980_ = _args[15];
lean_object* v___y_4981_ = _args[16];
lean_object* v___y_4982_ = _args[17];
_start:
{
size_t v_sz_boxed_4983_; size_t v_i_boxed_4984_; lean_object* v_res_4985_; 
v_sz_boxed_4983_ = lean_unbox_usize(v_sz_4968_);
lean_dec(v_sz_4968_);
v_i_boxed_4984_ = lean_unbox_usize(v_i_4969_);
lean_dec(v_i_4969_);
v_res_4985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(v___x_4965_, v___x_4966_, v_as_4967_, v_sz_boxed_4983_, v_i_boxed_4984_, v_b_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec(v___y_4972_);
lean_dec_ref(v___y_4971_);
lean_dec_ref(v_as_4967_);
lean_dec_ref(v___x_4965_);
return v_res_4985_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(lean_object* v_post_4993_){
_start:
{
lean_object* v___y_4995_; uint8_t v___x_5000_; 
v___x_5000_ = l_Lean_Expr_isLambda(v_post_4993_);
if (v___x_5000_ == 0)
{
v___y_4995_ = v_post_4993_;
goto v___jp_4994_;
}
else
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Lean_Expr_bindingBody_x21(v_post_4993_);
lean_dec_ref(v_post_4993_);
v___y_4995_ = v___x_5001_;
goto v___jp_4994_;
}
v___jp_4994_:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; uint8_t v___x_4999_; 
v___x_4996_ = l_Lean_Expr_consumeMData(v___y_4995_);
lean_dec_ref(v___y_4995_);
v___x_4997_ = l_Lean_Expr_getAppFn(v___x_4996_);
lean_dec_ref(v___x_4996_);
v___x_4998_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___closed__2));
v___x_4999_ = l_Lean_Expr_isConstOf(v___x_4997_, v___x_4998_);
lean_dec_ref(v___x_4997_);
return v___x_4999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost___boxed(lean_object* v_post_5002_){
_start:
{
uint8_t v_res_5003_; lean_object* v_r_5004_; 
v_res_5003_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(v_post_5002_);
v_r_5004_ = lean_box(v_res_5003_);
return v_r_5004_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(lean_object* v_a_5005_, lean_object* v_x_5006_){
_start:
{
if (lean_obj_tag(v_x_5006_) == 0)
{
uint8_t v___x_5007_; 
v___x_5007_ = 0;
return v___x_5007_;
}
else
{
lean_object* v_head_5008_; lean_object* v_tail_5009_; uint8_t v___x_5010_; 
v_head_5008_ = lean_ctor_get(v_x_5006_, 0);
v_tail_5009_ = lean_ctor_get(v_x_5006_, 1);
v___x_5010_ = lean_name_eq(v_a_5005_, v_head_5008_);
if (v___x_5010_ == 0)
{
v_x_5006_ = v_tail_5009_;
goto _start;
}
else
{
return v___x_5010_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0___boxed(lean_object* v_a_5012_, lean_object* v_x_5013_){
_start:
{
uint8_t v_res_5014_; lean_object* v_r_5015_; 
v_res_5014_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(v_a_5012_, v_x_5013_);
lean_dec(v_x_5013_);
lean_dec(v_a_5012_);
v_r_5015_ = lean_box(v_res_5014_);
return v_r_5015_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(lean_object* v_prog_5064_){
_start:
{
lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5065_ = l_Lean_Expr_getAppFn(v_prog_5064_);
v___x_5066_ = l_Lean_Expr_constName_x3f(v___x_5065_);
lean_dec_ref(v___x_5065_);
if (lean_obj_tag(v___x_5066_) == 0)
{
uint8_t v___x_5067_; 
v___x_5067_ = 0;
return v___x_5067_;
}
else
{
lean_object* v_val_5068_; lean_object* v___x_5069_; uint8_t v___x_5070_; 
v_val_5068_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_val_5068_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5069_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___closed__23));
v___x_5070_ = l_List_elem___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator_spec__0(v_val_5068_, v___x_5069_);
lean_dec(v_val_5068_);
return v___x_5070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator___boxed(lean_object* v_prog_5071_){
_start:
{
uint8_t v_res_5072_; lean_object* v_r_5073_; 
v_res_5072_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(v_prog_5071_);
lean_dec_ref(v_prog_5071_);
v_r_5073_ = lean_box(v_res_5072_);
return v_r_5073_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1(void){
_start:
{
lean_object* v___x_5075_; lean_object* v___x_5076_; 
v___x_5075_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__0));
v___x_5076_ = l_Lean_stringToMessageData(v___x_5075_);
return v___x_5076_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3(void){
_start:
{
lean_object* v___x_5078_; lean_object* v___x_5079_; 
v___x_5078_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__2));
v___x_5079_ = l_Lean_stringToMessageData(v___x_5078_);
return v___x_5079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(lean_object* v_goal_5080_, lean_object* v_info_5081_, lean_object* v_fp_5082_, lean_object* v_F_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_, lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_, lean_object* v_a_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v_mkOpAppM_5096_; lean_object* v___x_5097_; 
v_mkOpAppM_5096_ = lean_ctor_get(v_fp_5082_, 1);
lean_inc_ref(v_mkOpAppM_5096_);
lean_dec_ref(v_fp_5082_);
lean_inc(v_a_5094_);
lean_inc_ref(v_a_5093_);
lean_inc(v_a_5092_);
lean_inc_ref(v_a_5091_);
lean_inc_ref(v_info_5081_);
v___x_5097_ = lean_apply_6(v_mkOpAppM_5096_, v_info_5081_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_, lean_box(0));
if (lean_obj_tag(v___x_5097_) == 0)
{
lean_object* v_a_5098_; lean_object* v___x_5099_; 
v_a_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc(v_a_5098_);
lean_dec_ref_known(v___x_5097_, 1);
v___x_5099_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkFrameBackwardRuleCached___redArg(v_a_5098_, v_info_5081_, v_a_5085_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
if (lean_obj_tag(v___x_5099_) == 0)
{
lean_object* v_a_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
lean_inc(v_a_5100_);
lean_dec_ref_known(v___x_5099_, 1);
v___x_5101_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__1);
v___x_5102_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_5081_);
lean_dec_ref(v_info_5081_);
v___x_5103_ = l_Lean_indentExpr(v___x_5102_);
lean_inc_ref(v___x_5103_);
v___x_5104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5104_, 0, v___x_5101_);
lean_ctor_set(v___x_5104_, 1, v___x_5103_);
v___x_5105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5104_);
v___x_5106_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_5100_, v_goal_5080_, v___x_5105_, v_a_5084_, v_a_5085_, v_a_5086_, v_a_5087_, v_a_5088_, v_a_5089_, v_a_5090_, v_a_5091_, v_a_5092_, v_a_5093_, v_a_5094_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref_known(v___x_5106_, 1);
if (lean_obj_tag(v_a_5107_) == 1)
{
lean_object* v_mvarIds_5116_; 
v_mvarIds_5116_ = lean_ctor_get(v_a_5107_, 0);
lean_inc(v_mvarIds_5116_);
lean_dec_ref_known(v_a_5107_, 1);
if (lean_obj_tag(v_mvarIds_5116_) == 1)
{
lean_object* v_head_5117_; lean_object* v_tail_5118_; lean_object* v___x_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec_ref(v___x_5103_);
v_head_5117_ = lean_ctor_get(v_mvarIds_5116_, 0);
lean_inc(v_head_5117_);
v_tail_5118_ = lean_ctor_get(v_mvarIds_5116_, 1);
lean_inc(v_tail_5118_);
lean_dec_ref_known(v_mvarIds_5116_, 2);
v___x_5119_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_head_5117_, v_F_5083_, v_a_5092_);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5126_ == 0)
{
lean_object* v_unused_5127_; 
v_unused_5127_ = lean_ctor_get(v___x_5119_, 0);
lean_dec(v_unused_5127_);
v___x_5121_ = v___x_5119_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_dec(v___x_5119_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
lean_ctor_set(v___x_5121_, 0, v_tail_5118_);
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_tail_5118_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
else
{
lean_dec(v_mvarIds_5116_);
lean_dec_ref(v_F_5083_);
v___y_5109_ = v_a_5091_;
v___y_5110_ = v_a_5092_;
v___y_5111_ = v_a_5093_;
v___y_5112_ = v_a_5094_;
goto v___jp_5108_;
}
}
else
{
lean_dec(v_a_5107_);
lean_dec_ref(v_F_5083_);
v___y_5109_ = v_a_5091_;
v___y_5110_ = v_a_5092_;
v___y_5111_ = v_a_5093_;
v___y_5112_ = v_a_5094_;
goto v___jp_5108_;
}
v___jp_5108_:
{
lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
v___x_5113_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___closed__3);
v___x_5114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5113_);
lean_ctor_set(v___x_5114_, 1, v___x_5103_);
v___x_5115_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5114_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
return v___x_5115_;
}
}
else
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5135_; 
lean_dec_ref(v___x_5103_);
lean_dec_ref(v_F_5083_);
v_a_5128_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5135_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5135_ == 0)
{
v___x_5130_ = v___x_5106_;
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5106_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5135_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___x_5133_; 
if (v_isShared_5131_ == 0)
{
v___x_5133_ = v___x_5130_;
goto v_reusejp_5132_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v_a_5128_);
v___x_5133_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5132_;
}
v_reusejp_5132_:
{
return v___x_5133_;
}
}
}
}
else
{
lean_object* v_a_5136_; lean_object* v___x_5138_; uint8_t v_isShared_5139_; uint8_t v_isSharedCheck_5143_; 
lean_dec_ref(v_F_5083_);
lean_dec_ref(v_info_5081_);
lean_dec(v_goal_5080_);
v_a_5136_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5143_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5143_ == 0)
{
v___x_5138_ = v___x_5099_;
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
else
{
lean_inc(v_a_5136_);
lean_dec(v___x_5099_);
v___x_5138_ = lean_box(0);
v_isShared_5139_ = v_isSharedCheck_5143_;
goto v_resetjp_5137_;
}
v_resetjp_5137_:
{
lean_object* v___x_5141_; 
if (v_isShared_5139_ == 0)
{
v___x_5141_ = v___x_5138_;
goto v_reusejp_5140_;
}
else
{
lean_object* v_reuseFailAlloc_5142_; 
v_reuseFailAlloc_5142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_a_5136_);
v___x_5141_ = v_reuseFailAlloc_5142_;
goto v_reusejp_5140_;
}
v_reusejp_5140_:
{
return v___x_5141_;
}
}
}
}
else
{
lean_object* v_a_5144_; lean_object* v___x_5146_; uint8_t v_isShared_5147_; uint8_t v_isSharedCheck_5151_; 
lean_dec_ref(v_F_5083_);
lean_dec_ref(v_info_5081_);
lean_dec(v_goal_5080_);
v_a_5144_ = lean_ctor_get(v___x_5097_, 0);
v_isSharedCheck_5151_ = !lean_is_exclusive(v___x_5097_);
if (v_isSharedCheck_5151_ == 0)
{
v___x_5146_ = v___x_5097_;
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
else
{
lean_inc(v_a_5144_);
lean_dec(v___x_5097_);
v___x_5146_ = lean_box(0);
v_isShared_5147_ = v_isSharedCheck_5151_;
goto v_resetjp_5145_;
}
v_resetjp_5145_:
{
lean_object* v___x_5149_; 
if (v_isShared_5147_ == 0)
{
v___x_5149_ = v___x_5146_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
v___x_5149_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
return v___x_5149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule___boxed(lean_object* v_goal_5152_, lean_object* v_info_5153_, lean_object* v_fp_5154_, lean_object* v_F_5155_, lean_object* v_a_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_, lean_object* v_a_5159_, lean_object* v_a_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_, lean_object* v_a_5163_, lean_object* v_a_5164_, lean_object* v_a_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5152_, v_info_5153_, v_fp_5154_, v_F_5155_, v_a_5156_, v_a_5157_, v_a_5158_, v_a_5159_, v_a_5160_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_);
lean_dec(v_a_5166_);
lean_dec_ref(v_a_5165_);
lean_dec(v_a_5164_);
lean_dec_ref(v_a_5163_);
lean_dec(v_a_5162_);
lean_dec_ref(v_a_5161_);
lean_dec(v_a_5160_);
lean_dec_ref(v_a_5159_);
lean_dec(v_a_5158_);
lean_dec(v_a_5157_);
lean_dec_ref(v_a_5156_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(lean_object* v_as_x27_5172_, lean_object* v_b_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_){
_start:
{
if (lean_obj_tag(v_as_x27_5172_) == 0)
{
lean_object* v___x_5181_; 
v___x_5181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5181_, 0, v_b_5173_);
return v___x_5181_;
}
else
{
lean_object* v_head_5182_; lean_object* v_tail_5183_; lean_object* v___x_5184_; 
lean_dec_ref(v_b_5173_);
v_head_5182_ = lean_ctor_get(v_as_x27_5172_, 0);
v_tail_5183_ = lean_ctor_get(v_as_x27_5172_, 1);
lean_inc(v_head_5182_);
v___x_5184_ = l_Lean_MVarId_getType(v_head_5182_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v_a_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; uint8_t v___x_5189_; 
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_a_5185_);
lean_dec_ref_known(v___x_5184_, 1);
v___x_5186_ = lean_box(0);
v___x_5187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5188_ = lean_unsigned_to_nat(4u);
v___x_5189_ = l_Lean_Expr_isAppOfArity(v_a_5185_, v___x_5187_, v___x_5188_);
if (v___x_5189_ == 0)
{
lean_object* v___x_5190_; 
lean_dec(v_a_5185_);
v___x_5190_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0));
v_as_x27_5172_ = v_tail_5183_;
v_b_5173_ = v___x_5190_;
goto _start;
}
else
{
lean_object* v___x_5192_; lean_object* v___x_5193_; 
v___x_5192_ = l_Lean_Expr_appArg_x21(v_a_5185_);
lean_dec(v_a_5185_);
v___x_5193_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v___x_5192_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, v___y_5178_, v___y_5179_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5204_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5196_ = v___x_5193_;
v_isShared_5197_ = v_isSharedCheck_5204_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5193_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5204_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5202_; 
v___x_5198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5198_, 0, v_a_5194_);
v___x_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5199_, 0, v___x_5198_);
v___x_5200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
lean_ctor_set(v___x_5200_, 1, v___x_5186_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v___x_5200_);
v___x_5202_ = v___x_5196_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v___x_5200_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
else
{
lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
v_a_5205_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5193_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5193_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
}
else
{
lean_object* v_a_5213_; lean_object* v___x_5215_; uint8_t v_isShared_5216_; uint8_t v_isSharedCheck_5220_; 
v_a_5213_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5215_ = v___x_5184_;
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
else
{
lean_inc(v_a_5213_);
lean_dec(v___x_5184_);
v___x_5215_ = lean_box(0);
v_isShared_5216_ = v_isSharedCheck_5220_;
goto v_resetjp_5214_;
}
v_resetjp_5214_:
{
lean_object* v___x_5218_; 
if (v_isShared_5216_ == 0)
{
v___x_5218_ = v___x_5215_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_a_5213_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_5221_, lean_object* v_b_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(v_as_x27_5221_, v_b_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_);
lean_dec(v___y_5228_);
lean_dec_ref(v___y_5227_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v_as_x27_5221_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(lean_object* v_subgoals_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_, lean_object* v_a_5235_, lean_object* v_a_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_){
_start:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5244_ = lean_box(0);
v___x_5245_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg___closed__0));
v___x_5246_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(v_subgoals_5231_, v___x_5245_, v_a_5237_, v_a_5238_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
if (lean_obj_tag(v___x_5246_) == 0)
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5259_; 
v_a_5247_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5249_ = v___x_5246_;
v_isShared_5250_ = v_isSharedCheck_5259_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5246_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5259_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v_fst_5251_; 
v_fst_5251_ = lean_ctor_get(v_a_5247_, 0);
lean_inc(v_fst_5251_);
lean_dec(v_a_5247_);
if (lean_obj_tag(v_fst_5251_) == 0)
{
lean_object* v___x_5253_; 
if (v_isShared_5250_ == 0)
{
lean_ctor_set(v___x_5249_, 0, v___x_5244_);
v___x_5253_ = v___x_5249_;
goto v_reusejp_5252_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___x_5244_);
v___x_5253_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5252_;
}
v_reusejp_5252_:
{
return v___x_5253_;
}
}
else
{
lean_object* v_val_5255_; lean_object* v___x_5257_; 
v_val_5255_ = lean_ctor_get(v_fst_5251_, 0);
lean_inc(v_val_5255_);
lean_dec_ref_known(v_fst_5251_, 1);
if (v_isShared_5250_ == 0)
{
lean_ctor_set(v___x_5249_, 0, v_val_5255_);
v___x_5257_ = v___x_5249_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_val_5255_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
else
{
lean_object* v_a_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5267_; 
v_a_5260_ = lean_ctor_get(v___x_5246_, 0);
v_isSharedCheck_5267_ = !lean_is_exclusive(v___x_5246_);
if (v_isSharedCheck_5267_ == 0)
{
v___x_5262_ = v___x_5246_;
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_a_5260_);
lean_dec(v___x_5246_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5267_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v___x_5265_; 
if (v_isShared_5263_ == 0)
{
v___x_5265_ = v___x_5262_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5266_; 
v_reuseFailAlloc_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5266_, 0, v_a_5260_);
v___x_5265_ = v_reuseFailAlloc_5266_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
return v___x_5265_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f___boxed(lean_object* v_subgoals_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_, lean_object* v_a_5273_, lean_object* v_a_5274_, lean_object* v_a_5275_, lean_object* v_a_5276_, lean_object* v_a_5277_, lean_object* v_a_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(v_subgoals_5268_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
lean_dec(v_a_5279_);
lean_dec_ref(v_a_5278_);
lean_dec(v_a_5277_);
lean_dec_ref(v_a_5276_);
lean_dec(v_a_5275_);
lean_dec_ref(v_a_5274_);
lean_dec(v_a_5273_);
lean_dec_ref(v_a_5272_);
lean_dec(v_a_5271_);
lean_dec(v_a_5270_);
lean_dec_ref(v_a_5269_);
lean_dec(v_subgoals_5268_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0(lean_object* v_as_5282_, lean_object* v_as_x27_5283_, lean_object* v_b_5284_, lean_object* v_a_5285_, lean_object* v___y_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_, lean_object* v___y_5296_){
_start:
{
lean_object* v___x_5298_; 
v___x_5298_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___redArg(v_as_x27_5283_, v_b_5284_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_);
return v___x_5298_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0___boxed(lean_object* v_as_5299_, lean_object* v_as_x27_5300_, lean_object* v_b_5301_, lean_object* v_a_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_, lean_object* v___y_5308_, lean_object* v___y_5309_, lean_object* v___y_5310_, lean_object* v___y_5311_, lean_object* v___y_5312_, lean_object* v___y_5313_, lean_object* v___y_5314_){
_start:
{
lean_object* v_res_5315_; 
v_res_5315_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f_spec__0(v_as_5299_, v_as_x27_5300_, v_b_5301_, v_a_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_, v___y_5308_, v___y_5309_, v___y_5310_, v___y_5311_, v___y_5312_, v___y_5313_);
lean_dec(v___y_5313_);
lean_dec_ref(v___y_5312_);
lean_dec(v___y_5311_);
lean_dec_ref(v___y_5310_);
lean_dec(v___y_5309_);
lean_dec_ref(v___y_5308_);
lean_dec(v___y_5307_);
lean_dec_ref(v___y_5306_);
lean_dec(v___y_5305_);
lean_dec(v___y_5304_);
lean_dec_ref(v___y_5303_);
lean_dec(v_as_x27_5300_);
lean_dec(v_as_5299_);
return v_res_5315_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(lean_object* v_a_5316_, lean_object* v_x_5317_){
_start:
{
if (lean_obj_tag(v_x_5317_) == 0)
{
lean_object* v___x_5318_; 
v___x_5318_ = lean_box(0);
return v___x_5318_;
}
else
{
lean_object* v_key_5319_; lean_object* v_value_5320_; lean_object* v_tail_5321_; uint8_t v___x_5322_; 
v_key_5319_ = lean_ctor_get(v_x_5317_, 0);
v_value_5320_ = lean_ctor_get(v_x_5317_, 1);
v_tail_5321_ = lean_ctor_get(v_x_5317_, 2);
v___x_5322_ = lean_name_eq(v_key_5319_, v_a_5316_);
if (v___x_5322_ == 0)
{
v_x_5317_ = v_tail_5321_;
goto _start;
}
else
{
lean_object* v___x_5324_; 
lean_inc(v_value_5320_);
v___x_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5324_, 0, v_value_5320_);
return v___x_5324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg___boxed(lean_object* v_a_5325_, lean_object* v_x_5326_){
_start:
{
lean_object* v_res_5327_; 
v_res_5327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(v_a_5325_, v_x_5326_);
lean_dec(v_x_5326_);
lean_dec(v_a_5325_);
return v_res_5327_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5328_; uint64_t v___x_5329_; 
v___x_5328_ = lean_unsigned_to_nat(1723u);
v___x_5329_ = lean_uint64_of_nat(v___x_5328_);
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(lean_object* v_m_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v_buckets_5332_; lean_object* v___x_5333_; uint64_t v___y_5335_; 
v_buckets_5332_ = lean_ctor_get(v_m_5330_, 1);
v___x_5333_ = lean_array_get_size(v_buckets_5332_);
if (lean_obj_tag(v_a_5331_) == 0)
{
uint64_t v___x_5349_; 
v___x_5349_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___closed__0);
v___y_5335_ = v___x_5349_;
goto v___jp_5334_;
}
else
{
uint64_t v_hash_5350_; 
v_hash_5350_ = lean_ctor_get_uint64(v_a_5331_, sizeof(void*)*2);
v___y_5335_ = v_hash_5350_;
goto v___jp_5334_;
}
v___jp_5334_:
{
uint64_t v___x_5336_; uint64_t v___x_5337_; uint64_t v_fold_5338_; uint64_t v___x_5339_; uint64_t v___x_5340_; uint64_t v___x_5341_; size_t v___x_5342_; size_t v___x_5343_; size_t v___x_5344_; size_t v___x_5345_; size_t v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; 
v___x_5336_ = 32ULL;
v___x_5337_ = lean_uint64_shift_right(v___y_5335_, v___x_5336_);
v_fold_5338_ = lean_uint64_xor(v___y_5335_, v___x_5337_);
v___x_5339_ = 16ULL;
v___x_5340_ = lean_uint64_shift_right(v_fold_5338_, v___x_5339_);
v___x_5341_ = lean_uint64_xor(v_fold_5338_, v___x_5340_);
v___x_5342_ = lean_uint64_to_usize(v___x_5341_);
v___x_5343_ = lean_usize_of_nat(v___x_5333_);
v___x_5344_ = ((size_t)1ULL);
v___x_5345_ = lean_usize_sub(v___x_5343_, v___x_5344_);
v___x_5346_ = lean_usize_land(v___x_5342_, v___x_5345_);
v___x_5347_ = lean_array_uget_borrowed(v_buckets_5332_, v___x_5346_);
v___x_5348_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(v_a_5331_, v___x_5347_);
return v___x_5348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg___boxed(lean_object* v_m_5351_, lean_object* v_a_5352_){
_start:
{
lean_object* v_res_5353_; 
v_res_5353_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(v_m_5351_, v_a_5352_);
lean_dec(v_a_5352_);
lean_dec_ref(v_m_5351_);
return v_res_5353_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5355_; lean_object* v___x_5356_; 
v___x_5355_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__0));
v___x_5356_ = l_Lean_stringToMessageData(v___x_5355_);
return v___x_5356_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5358_; lean_object* v___x_5359_; 
v___x_5358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__2));
v___x_5359_ = l_Lean_stringToMessageData(v___x_5358_);
return v___x_5359_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
v___x_5361_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__4));
v___x_5362_ = l_Lean_stringToMessageData(v___x_5361_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0(lean_object* v_scope_5363_, lean_object* v___x_5364_, lean_object* v___x_5365_, lean_object* v_goal_5366_, lean_object* v_info_5367_, lean_object* v_pre_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_){
_start:
{
lean_object* v___x_5381_; 
lean_inc_ref(v___x_5365_);
lean_inc_ref(v___x_5364_);
v___x_5381_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_findSpec___redArg(v_scope_5363_, v___x_5364_, v___x_5365_, v___y_5369_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5381_) == 0)
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5592_; 
v_a_5382_ = lean_ctor_get(v___x_5381_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5381_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5384_ = v___x_5381_;
v_isShared_5385_ = v_isSharedCheck_5592_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5381_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5592_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v_fst_5386_; lean_object* v_snd_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5591_; 
v_fst_5386_ = lean_ctor_get(v_a_5382_, 0);
v_snd_5387_ = lean_ctor_get(v_a_5382_, 1);
v_isSharedCheck_5591_ = !lean_is_exclusive(v_a_5382_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5389_ = v_a_5382_;
v_isShared_5390_ = v_isSharedCheck_5591_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_snd_5387_);
lean_inc(v_fst_5386_);
lean_dec(v_a_5382_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5591_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___y_5392_; lean_object* v___y_5400_; lean_object* v___y_5401_; lean_object* v___y_5402_; lean_object* v___y_5403_; lean_object* v___y_5404_; lean_object* v___y_5405_; lean_object* v___y_5406_; lean_object* v___y_5407_; lean_object* v___y_5408_; lean_object* v___y_5409_; lean_object* v___y_5410_; lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v___y_5413_; 
if (lean_obj_tag(v_snd_5387_) == 0)
{
lean_object* v_a_5441_; lean_object* v___x_5443_; uint8_t v_isShared_5444_; uint8_t v_isSharedCheck_5448_; 
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5365_);
lean_dec_ref(v___x_5364_);
v_a_5441_ = lean_ctor_get(v_snd_5387_, 0);
v_isSharedCheck_5448_ = !lean_is_exclusive(v_snd_5387_);
if (v_isSharedCheck_5448_ == 0)
{
v___x_5443_ = v_snd_5387_;
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
else
{
lean_inc(v_a_5441_);
lean_dec(v_snd_5387_);
v___x_5443_ = lean_box(0);
v_isShared_5444_ = v_isSharedCheck_5448_;
goto v_resetjp_5442_;
}
v_resetjp_5442_:
{
lean_object* v___x_5446_; 
if (v_isShared_5444_ == 0)
{
v___x_5446_ = v___x_5443_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_a_5441_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
else
{
lean_object* v_a_5449_; lean_object* v___y_5451_; uint8_t v___y_5579_; uint8_t v___x_5588_; 
v_a_5449_ = lean_ctor_get(v_snd_5387_, 0);
lean_inc(v_a_5449_);
lean_dec_ref_known(v_snd_5387_, 1);
v___x_5588_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isStructuralCombinator(v___x_5364_);
if (v___x_5588_ == 0)
{
lean_object* v___x_5589_; uint8_t v___x_5590_; 
v___x_5589_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(v_info_5367_);
v___x_5590_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isFramedPost(v___x_5589_);
v___y_5579_ = v___x_5590_;
goto v___jp_5578_;
}
else
{
v___y_5579_ = v___x_5588_;
goto v___jp_5578_;
}
v___jp_5450_:
{
lean_object* v_resourceTy_5452_; lean_object* v_proc_5453_; lean_object* v___x_5454_; 
v_resourceTy_5452_ = lean_ctor_get(v___y_5451_, 2);
v_proc_5453_ = lean_ctor_get(v___y_5451_, 4);
lean_inc_ref(v_resourceTy_5452_);
lean_inc(v___y_5379_);
lean_inc_ref(v___y_5378_);
lean_inc(v___y_5377_);
lean_inc_ref(v___y_5376_);
lean_inc_ref(v_info_5367_);
v___x_5454_ = lean_apply_6(v_resourceTy_5452_, v_info_5367_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, lean_box(0));
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; lean_object* v___x_5456_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc_n(v_a_5455_, 2);
lean_dec_ref_known(v___x_5454_, 1);
v___x_5456_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_a_5455_, v_info_5367_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
lean_inc(v_a_5457_);
lean_dec_ref_known(v___x_5456_, 1);
if (lean_obj_tag(v_a_5457_) == 1)
{
lean_object* v_val_5458_; lean_object* v___x_5459_; 
lean_dec(v_a_5455_);
lean_dec(v_a_5449_);
lean_del_object(v___x_5389_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v___x_5364_);
v_val_5458_ = lean_ctor_get(v_a_5457_, 0);
lean_inc(v_val_5458_);
lean_dec_ref_known(v_a_5457_, 1);
v___x_5459_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5366_, v_info_5367_, v___y_5451_, v_val_5458_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5468_; 
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5468_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5468_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5464_; lean_object* v___x_5466_; 
v___x_5464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5464_, 0, v_fst_5386_);
lean_ctor_set(v___x_5464_, 1, v_a_5460_);
if (v_isShared_5463_ == 0)
{
lean_ctor_set(v___x_5462_, 0, v___x_5464_);
v___x_5466_ = v___x_5462_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v___x_5464_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
else
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5476_; 
lean_dec(v_fst_5386_);
v_a_5469_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5476_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5476_ == 0)
{
v___x_5471_ = v___x_5459_;
v_isShared_5472_ = v_isSharedCheck_5476_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5459_);
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
else
{
lean_dec(v_a_5457_);
if (lean_obj_tag(v_proc_5453_) == 1)
{
lean_object* v_val_5477_; lean_object* v___x_5478_; 
v_val_5477_ = lean_ctor_get(v_proc_5453_, 0);
v___x_5478_ = l_Lean_Meta_saveState___redArg(v___y_5377_, v___y_5379_);
if (lean_obj_tag(v___x_5478_) == 0)
{
lean_object* v_a_5479_; lean_object* v___x_5480_; 
v_a_5479_ = lean_ctor_get(v___x_5478_, 0);
lean_inc(v_a_5479_);
lean_dec_ref_known(v___x_5478_, 1);
lean_inc_ref(v_info_5367_);
lean_inc(v_goal_5366_);
lean_inc(v_fst_5386_);
v___x_5480_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_fst_5386_, v_goal_5366_, v_info_5367_, v_a_5449_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5480_) == 0)
{
lean_object* v_a_5481_; 
v_a_5481_ = lean_ctor_get(v___x_5480_, 0);
lean_inc(v_a_5481_);
lean_dec_ref_known(v___x_5480_, 1);
if (lean_obj_tag(v_a_5481_) == 0)
{
lean_object* v_subgoals_5482_; lean_object* v___x_5484_; uint8_t v_isShared_5485_; uint8_t v_isSharedCheck_5543_; 
v_subgoals_5482_ = lean_ctor_get(v_a_5481_, 1);
v_isSharedCheck_5543_ = !lean_is_exclusive(v_a_5481_);
if (v_isSharedCheck_5543_ == 0)
{
lean_object* v_unused_5544_; 
v_unused_5544_ = lean_ctor_get(v_a_5481_, 0);
lean_dec(v_unused_5544_);
v___x_5484_ = v_a_5481_;
v_isShared_5485_ = v_isSharedCheck_5543_;
goto v_resetjp_5483_;
}
else
{
lean_inc(v_subgoals_5482_);
lean_dec(v_a_5481_);
v___x_5484_ = lean_box(0);
v_isShared_5485_ = v_isSharedCheck_5543_;
goto v_resetjp_5483_;
}
v_resetjp_5483_:
{
lean_object* v___x_5486_; 
v___x_5486_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_specPreOf_x3f(v_subgoals_5482_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5486_) == 0)
{
lean_object* v_a_5487_; 
v_a_5487_ = lean_ctor_get(v___x_5486_, 0);
lean_inc(v_a_5487_);
lean_dec_ref_known(v___x_5486_, 1);
if (lean_obj_tag(v_a_5487_) == 0)
{
lean_del_object(v___x_5484_);
lean_dec(v_a_5479_);
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v___y_5392_ = v_subgoals_5482_;
goto v___jp_5391_;
}
else
{
lean_object* v_val_5488_; lean_object* v___x_5489_; 
v_val_5488_ = lean_ctor_get(v_a_5487_, 0);
lean_inc(v_val_5488_);
lean_dec_ref_known(v_a_5487_, 1);
lean_inc(v_val_5477_);
lean_inc(v___y_5379_);
lean_inc_ref(v___y_5378_);
lean_inc(v___y_5377_);
lean_inc_ref(v___y_5376_);
lean_inc(v___y_5375_);
lean_inc_ref(v___y_5374_);
lean_inc_ref(v_info_5367_);
v___x_5489_ = lean_apply_11(v_val_5477_, v_a_5455_, v_pre_5368_, v_info_5367_, v_val_5488_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, lean_box(0));
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v_a_5490_; 
v_a_5490_ = lean_ctor_get(v___x_5489_, 0);
lean_inc(v_a_5490_);
lean_dec_ref_known(v___x_5489_, 1);
if (lean_obj_tag(v_a_5490_) == 1)
{
lean_object* v_val_5491_; lean_object* v___x_5492_; 
lean_dec(v_subgoals_5482_);
lean_del_object(v___x_5389_);
lean_del_object(v___x_5384_);
v_val_5491_ = lean_ctor_get(v_a_5490_, 0);
lean_inc(v_val_5491_);
lean_dec_ref_known(v_a_5490_, 1);
v___x_5492_ = l_Lean_Meta_Sym_instantiateMVarsS(v_val_5491_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_options_5493_; uint8_t v_hasTrace_5494_; 
v_options_5493_ = lean_ctor_get(v___y_5378_, 2);
v_hasTrace_5494_ = lean_ctor_get_uint8(v_options_5493_, sizeof(void*)*1);
if (v_hasTrace_5494_ == 0)
{
lean_object* v_a_5495_; 
lean_del_object(v___x_5484_);
lean_dec_ref(v___x_5364_);
v_a_5495_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5495_);
lean_dec_ref_known(v___x_5492_, 1);
v___y_5400_ = v___y_5451_;
v___y_5401_ = v_a_5479_;
v___y_5402_ = v_a_5495_;
v___y_5403_ = v___y_5369_;
v___y_5404_ = v___y_5370_;
v___y_5405_ = v___y_5371_;
v___y_5406_ = v___y_5372_;
v___y_5407_ = v___y_5373_;
v___y_5408_ = v___y_5374_;
v___y_5409_ = v___y_5375_;
v___y_5410_ = v___y_5376_;
v___y_5411_ = v___y_5377_;
v___y_5412_ = v___y_5378_;
v___y_5413_ = v___y_5379_;
goto v___jp_5399_;
}
else
{
lean_object* v_a_5496_; lean_object* v_inheritedTraceOptions_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; uint8_t v___x_5500_; 
v_a_5496_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5496_);
lean_dec_ref_known(v___x_5492_, 1);
v_inheritedTraceOptions_5497_ = lean_ctor_get(v___y_5378_, 13);
v___x_5498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_5499_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5497_, v_options_5493_, v___x_5499_);
if (v___x_5500_ == 0)
{
lean_del_object(v___x_5484_);
lean_dec_ref(v___x_5364_);
v___y_5400_ = v___y_5451_;
v___y_5401_ = v_a_5479_;
v___y_5402_ = v_a_5496_;
v___y_5403_ = v___y_5369_;
v___y_5404_ = v___y_5370_;
v___y_5405_ = v___y_5371_;
v___y_5406_ = v___y_5372_;
v___y_5407_ = v___y_5373_;
v___y_5408_ = v___y_5374_;
v___y_5409_ = v___y_5375_;
v___y_5410_ = v___y_5376_;
v___y_5411_ = v___y_5377_;
v___y_5412_ = v___y_5378_;
v___y_5413_ = v___y_5379_;
goto v___jp_5399_;
}
else
{
lean_object* v___x_5501_; lean_object* v___x_5502_; lean_object* v___x_5504_; 
v___x_5501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__1);
v___x_5502_ = l_Lean_MessageData_ofExpr(v___x_5364_);
if (v_isShared_5485_ == 0)
{
lean_ctor_set_tag(v___x_5484_, 7);
lean_ctor_set(v___x_5484_, 1, v___x_5502_);
lean_ctor_set(v___x_5484_, 0, v___x_5501_);
v___x_5504_ = v___x_5484_;
goto v_reusejp_5503_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5501_);
lean_ctor_set(v_reuseFailAlloc_5518_, 1, v___x_5502_);
v___x_5504_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5503_;
}
v_reusejp_5503_:
{
lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5505_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3);
v___x_5506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5506_, 0, v___x_5504_);
lean_ctor_set(v___x_5506_, 1, v___x_5505_);
lean_inc(v_a_5496_);
v___x_5507_ = l_Lean_indentExpr(v_a_5496_);
v___x_5508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5508_, 0, v___x_5506_);
lean_ctor_set(v___x_5508_, 1, v___x_5507_);
v___x_5509_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5498_, v___x_5508_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_dec_ref_known(v___x_5509_, 1);
v___y_5400_ = v___y_5451_;
v___y_5401_ = v_a_5479_;
v___y_5402_ = v_a_5496_;
v___y_5403_ = v___y_5369_;
v___y_5404_ = v___y_5370_;
v___y_5405_ = v___y_5371_;
v___y_5406_ = v___y_5372_;
v___y_5407_ = v___y_5373_;
v___y_5408_ = v___y_5374_;
v___y_5409_ = v___y_5375_;
v___y_5410_ = v___y_5376_;
v___y_5411_ = v___y_5377_;
v___y_5412_ = v___y_5378_;
v___y_5413_ = v___y_5379_;
goto v___jp_5399_;
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec(v_a_5496_);
lean_dec(v_a_5479_);
lean_dec_ref(v___y_5451_);
lean_dec(v_fst_5386_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5509_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5509_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_del_object(v___x_5484_);
lean_dec(v_a_5479_);
lean_dec_ref(v___y_5451_);
lean_dec(v_fst_5386_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v_a_5519_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5492_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5492_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
else
{
lean_dec(v_a_5490_);
lean_del_object(v___x_5484_);
lean_dec(v_a_5479_);
lean_dec_ref(v___y_5451_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v___y_5392_ = v_subgoals_5482_;
goto v___jp_5391_;
}
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
lean_del_object(v___x_5484_);
lean_dec(v_subgoals_5482_);
lean_dec(v_a_5479_);
lean_dec_ref(v___y_5451_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v_a_5527_ = lean_ctor_get(v___x_5489_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5489_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___x_5489_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___x_5489_);
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
}
else
{
lean_object* v_a_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5542_; 
lean_del_object(v___x_5484_);
lean_dec(v_subgoals_5482_);
lean_dec(v_a_5479_);
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v_a_5535_ = lean_ctor_get(v___x_5486_, 0);
v_isSharedCheck_5542_ = !lean_is_exclusive(v___x_5486_);
if (v_isSharedCheck_5542_ == 0)
{
v___x_5537_ = v___x_5486_;
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_a_5535_);
lean_dec(v___x_5486_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5542_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5540_; 
if (v_isShared_5538_ == 0)
{
v___x_5540_ = v___x_5537_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v_a_5535_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
}
else
{
lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; 
lean_dec(v_a_5481_);
lean_dec(v_a_5479_);
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
v___x_5545_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__3);
v___x_5546_ = l_Lean_indentExpr(v___x_5364_);
v___x_5547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5547_, 0, v___x_5545_);
lean_ctor_set(v___x_5547_, 1, v___x_5546_);
v___x_5548_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___closed__5);
v___x_5549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5547_);
lean_ctor_set(v___x_5549_, 1, v___x_5548_);
v___x_5550_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5549_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
return v___x_5550_;
}
}
else
{
lean_dec(v_a_5479_);
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
return v___x_5480_;
}
}
else
{
lean_object* v_a_5551_; lean_object* v___x_5553_; uint8_t v_isShared_5554_; uint8_t v_isSharedCheck_5558_; 
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_dec(v_a_5449_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v_a_5551_ = lean_ctor_get(v___x_5478_, 0);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5478_);
if (v_isSharedCheck_5558_ == 0)
{
v___x_5553_ = v___x_5478_;
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
else
{
lean_inc(v_a_5551_);
lean_dec(v___x_5478_);
v___x_5553_ = lean_box(0);
v_isShared_5554_ = v_isSharedCheck_5558_;
goto v_resetjp_5552_;
}
v_resetjp_5552_:
{
lean_object* v___x_5556_; 
if (v_isShared_5554_ == 0)
{
v___x_5556_ = v___x_5553_;
goto v_reusejp_5555_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_a_5551_);
v___x_5556_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5555_;
}
v_reusejp_5555_:
{
return v___x_5556_;
}
}
}
}
else
{
lean_object* v___x_5559_; 
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_del_object(v___x_5389_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v___x_5364_);
v___x_5559_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_fst_5386_, v_goal_5366_, v_info_5367_, v_a_5449_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
return v___x_5559_;
}
}
}
else
{
lean_object* v_a_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5567_; 
lean_dec(v_a_5455_);
lean_dec_ref(v___y_5451_);
lean_dec(v_a_5449_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v_a_5560_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5567_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5567_ == 0)
{
v___x_5562_ = v___x_5456_;
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_a_5560_);
lean_dec(v___x_5456_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5567_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5565_; 
if (v_isShared_5563_ == 0)
{
v___x_5565_ = v___x_5562_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5566_; 
v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
v___x_5565_ = v_reuseFailAlloc_5566_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
return v___x_5565_;
}
}
}
}
else
{
lean_object* v_a_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
lean_dec_ref(v___y_5451_);
lean_dec(v_a_5449_);
lean_del_object(v___x_5389_);
lean_dec(v_fst_5386_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5364_);
v_a_5568_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5575_ == 0)
{
v___x_5570_ = v___x_5454_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_a_5568_);
lean_dec(v___x_5454_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5568_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
}
}
}
}
v___jp_5576_:
{
lean_object* v___x_5577_; 
v___x_5577_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_meetFrameProc;
v___y_5451_ = v___x_5577_;
goto v___jp_5450_;
}
v___jp_5578_:
{
if (v___y_5579_ == 0)
{
lean_object* v___x_5580_; lean_object* v___x_5581_; 
v___x_5580_ = l_Lean_Expr_getAppFn(v___x_5365_);
lean_dec_ref(v___x_5365_);
v___x_5581_ = l_Lean_Expr_constName_x3f(v___x_5580_);
lean_dec_ref(v___x_5580_);
if (lean_obj_tag(v___x_5581_) == 0)
{
goto v___jp_5576_;
}
else
{
lean_object* v_frameProcs_5582_; lean_object* v_val_5583_; lean_object* v_byProg_5584_; lean_object* v___x_5585_; 
v_frameProcs_5582_ = lean_ctor_get(v___y_5369_, 1);
v_val_5583_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_val_5583_);
lean_dec_ref_known(v___x_5581_, 1);
v_byProg_5584_ = lean_ctor_get(v_frameProcs_5582_, 0);
v___x_5585_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(v_byProg_5584_, v_val_5583_);
lean_dec(v_val_5583_);
if (lean_obj_tag(v___x_5585_) == 0)
{
goto v___jp_5576_;
}
else
{
lean_object* v_val_5586_; 
v_val_5586_ = lean_ctor_get(v___x_5585_, 0);
lean_inc(v_val_5586_);
lean_dec_ref_known(v___x_5585_, 1);
v___y_5451_ = v_val_5586_;
goto v___jp_5450_;
}
}
}
else
{
lean_object* v___x_5587_; 
lean_del_object(v___x_5389_);
lean_del_object(v___x_5384_);
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v___x_5365_);
lean_dec_ref(v___x_5364_);
v___x_5587_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_fst_5386_, v_goal_5366_, v_info_5367_, v_a_5449_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
return v___x_5587_;
}
}
}
v___jp_5391_:
{
lean_object* v___x_5394_; 
if (v_isShared_5390_ == 0)
{
lean_ctor_set(v___x_5389_, 1, v___y_5392_);
v___x_5394_ = v___x_5389_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v_fst_5386_);
lean_ctor_set(v_reuseFailAlloc_5398_, 1, v___y_5392_);
v___x_5394_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5396_; 
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 0, v___x_5394_);
v___x_5396_ = v___x_5384_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v___x_5394_);
v___x_5396_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
return v___x_5396_;
}
}
}
v___jp_5399_:
{
lean_object* v___x_5414_; 
v___x_5414_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5401_, v___y_5411_, v___y_5413_);
lean_dec_ref(v___y_5401_);
if (lean_obj_tag(v___x_5414_) == 0)
{
lean_object* v___x_5415_; 
lean_dec_ref_known(v___x_5414_, 1);
v___x_5415_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameRule(v_goal_5366_, v_info_5367_, v___y_5400_, v___y_5402_, v___y_5403_, v___y_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_);
if (lean_obj_tag(v___x_5415_) == 0)
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5424_; 
v_a_5416_ = lean_ctor_get(v___x_5415_, 0);
v_isSharedCheck_5424_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5424_ == 0)
{
v___x_5418_ = v___x_5415_;
v_isShared_5419_ = v_isSharedCheck_5424_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5415_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5424_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5420_; lean_object* v___x_5422_; 
v___x_5420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5420_, 0, v_fst_5386_);
lean_ctor_set(v___x_5420_, 1, v_a_5416_);
if (v_isShared_5419_ == 0)
{
lean_ctor_set(v___x_5418_, 0, v___x_5420_);
v___x_5422_ = v___x_5418_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5423_; 
v_reuseFailAlloc_5423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5423_, 0, v___x_5420_);
v___x_5422_ = v_reuseFailAlloc_5423_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
return v___x_5422_;
}
}
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
lean_dec(v_fst_5386_);
v_a_5425_ = lean_ctor_get(v___x_5415_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5415_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v___x_5415_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5415_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
else
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
lean_dec_ref(v___y_5402_);
lean_dec_ref(v___y_5400_);
lean_dec(v_fst_5386_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
v_a_5433_ = lean_ctor_get(v___x_5414_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v___x_5414_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5435_ = v___x_5414_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5414_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5600_; 
lean_dec_ref(v_pre_5368_);
lean_dec_ref(v_info_5367_);
lean_dec(v_goal_5366_);
lean_dec_ref(v___x_5365_);
lean_dec_ref(v___x_5364_);
v_a_5593_ = lean_ctor_get(v___x_5381_, 0);
v_isSharedCheck_5600_ = !lean_is_exclusive(v___x_5381_);
if (v_isSharedCheck_5600_ == 0)
{
v___x_5595_ = v___x_5381_;
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5381_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5600_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5596_ == 0)
{
v___x_5598_ = v___x_5595_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5599_; 
v_reuseFailAlloc_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5599_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5599_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
return v___x_5598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___boxed(lean_object** _args){
lean_object* v_scope_5601_ = _args[0];
lean_object* v___x_5602_ = _args[1];
lean_object* v___x_5603_ = _args[2];
lean_object* v_goal_5604_ = _args[3];
lean_object* v_info_5605_ = _args[4];
lean_object* v_pre_5606_ = _args[5];
lean_object* v___y_5607_ = _args[6];
lean_object* v___y_5608_ = _args[7];
lean_object* v___y_5609_ = _args[8];
lean_object* v___y_5610_ = _args[9];
lean_object* v___y_5611_ = _args[10];
lean_object* v___y_5612_ = _args[11];
lean_object* v___y_5613_ = _args[12];
lean_object* v___y_5614_ = _args[13];
lean_object* v___y_5615_ = _args[14];
lean_object* v___y_5616_ = _args[15];
lean_object* v___y_5617_ = _args[16];
lean_object* v___y_5618_ = _args[17];
_start:
{
lean_object* v_res_5619_; 
v_res_5619_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0(v_scope_5601_, v___x_5602_, v___x_5603_, v_goal_5604_, v_info_5605_, v_pre_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_);
lean_dec(v___y_5617_);
lean_dec_ref(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
lean_dec(v___y_5609_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
return v_res_5619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(lean_object* v_scope_5620_, lean_object* v_goal_5621_, lean_object* v_pre_5622_, lean_object* v_info_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_, lean_object* v_a_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_){
_start:
{
lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___f_5638_; lean_object* v___x_5639_; 
v___x_5636_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_5623_);
v___x_5637_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_5623_);
lean_inc(v_goal_5621_);
v___f_5638_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___lam__0___boxed), 18, 6);
lean_closure_set(v___f_5638_, 0, v_scope_5620_);
lean_closure_set(v___f_5638_, 1, v___x_5636_);
lean_closure_set(v___f_5638_, 2, v___x_5637_);
lean_closure_set(v___f_5638_, 3, v_goal_5621_);
lean_closure_set(v___f_5638_, 4, v_info_5623_);
lean_closure_set(v___f_5638_, 5, v_pre_5622_);
v___x_5639_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5621_, v___f_5638_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_, v_a_5630_, v_a_5631_, v_a_5632_, v_a_5633_, v_a_5634_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec___boxed(lean_object* v_scope_5640_, lean_object* v_goal_5641_, lean_object* v_pre_5642_, lean_object* v_info_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_){
_start:
{
lean_object* v_res_5656_; 
v_res_5656_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(v_scope_5640_, v_goal_5641_, v_pre_5642_, v_info_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_, v_a_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
lean_dec(v_a_5648_);
lean_dec_ref(v_a_5647_);
lean_dec(v_a_5646_);
lean_dec(v_a_5645_);
lean_dec_ref(v_a_5644_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0(lean_object* v_00_u03b2_5657_, lean_object* v_m_5658_, lean_object* v_a_5659_){
_start:
{
lean_object* v___x_5660_; 
v___x_5660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___redArg(v_m_5658_, v_a_5659_);
return v___x_5660_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0___boxed(lean_object* v_00_u03b2_5661_, lean_object* v_m_5662_, lean_object* v_a_5663_){
_start:
{
lean_object* v_res_5664_; 
v_res_5664_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0(v_00_u03b2_5661_, v_m_5662_, v_a_5663_);
lean_dec(v_a_5663_);
lean_dec_ref(v_m_5662_);
return v_res_5664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0(lean_object* v_00_u03b2_5665_, lean_object* v_a_5666_, lean_object* v_x_5667_){
_start:
{
lean_object* v___x_5668_; 
v___x_5668_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___redArg(v_a_5666_, v_x_5667_);
return v___x_5668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5669_, lean_object* v_a_5670_, lean_object* v_x_5671_){
_start:
{
lean_object* v_res_5672_; 
v_res_5672_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec_spec__0_spec__0(v_00_u03b2_5669_, v_a_5670_, v_x_5671_);
lean_dec(v_x_5671_);
lean_dec(v_a_5670_);
return v_res_5672_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5674_; lean_object* v___x_5675_; 
v___x_5674_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_5675_ = l_Lean_stringToMessageData(v___x_5674_);
return v___x_5675_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5677_; lean_object* v___x_5678_; 
v___x_5677_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2));
v___x_5678_ = l_Lean_stringToMessageData(v___x_5677_);
return v___x_5678_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5680_; lean_object* v___x_5681_; 
v___x_5680_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_5681_ = l_Lean_stringToMessageData(v___x_5680_);
return v___x_5681_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; 
v___x_5683_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6));
v___x_5684_ = l_Lean_stringToMessageData(v___x_5683_);
return v___x_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_5687_, lean_object* v_scope_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_){
_start:
{
lean_object* v_g_5702_; lean_object* v_gs_5708_; lean_object* v___y_5712_; lean_object* v___y_5713_; lean_object* v___y_5718_; lean_object* v_g_5719_; lean_object* v___y_5725_; lean_object* v_gs_5726_; lean_object* v___y_5730_; lean_object* v_g_5731_; lean_object* v___y_5732_; lean_object* v___y_5754_; lean_object* v___y_5755_; lean_object* v___y_5756_; lean_object* v___y_5757_; lean_object* v___y_5758_; lean_object* v___y_5759_; lean_object* v___y_5760_; lean_object* v___y_5761_; lean_object* v___y_5762_; lean_object* v___y_5763_; lean_object* v___y_5764_; lean_object* v___y_5765_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5779_; lean_object* v___y_5780_; lean_object* v___y_5781_; lean_object* v___y_5782_; lean_object* v___y_5783_; lean_object* v___y_5784_; lean_object* v___y_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5790_; lean_object* v___y_5791_; lean_object* v___y_5792_; lean_object* v___y_5793_; lean_object* v___x_5906_; 
v___x_5906_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_5690_);
if (lean_obj_tag(v___x_5906_) == 0)
{
lean_object* v_a_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_6158_; 
v_a_5907_ = lean_ctor_get(v___x_5906_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_5906_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_5909_ = v___x_5906_;
v_isShared_5910_ = v_isSharedCheck_6158_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_a_5907_);
lean_dec(v___x_5906_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_6158_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
uint8_t v___x_5911_; 
v___x_5911_ = lean_unbox(v_a_5907_);
lean_dec(v_a_5907_);
if (v___x_5911_ == 0)
{
lean_object* v___x_5912_; 
lean_del_object(v___x_5909_);
lean_inc(v_goal_5687_);
v___x_5912_ = l_Lean_MVarId_getType(v_goal_5687_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
if (lean_obj_tag(v___x_5912_) == 0)
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_6145_; 
v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_6145_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_6145_ == 0)
{
v___x_5915_ = v___x_5912_;
v_isShared_5916_ = v_isSharedCheck_6145_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5912_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_6145_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v_options_5923_; lean_object* v_inheritedTraceOptions_5924_; uint8_t v_hasTrace_5925_; lean_object* v___x_5926_; lean_object* v___y_5928_; lean_object* v___y_5929_; lean_object* v___y_5930_; lean_object* v___y_5931_; lean_object* v___y_5932_; lean_object* v___y_5933_; lean_object* v___y_5934_; lean_object* v___y_5935_; lean_object* v___y_5936_; lean_object* v___y_5937_; lean_object* v___y_5938_; 
v_options_5923_ = lean_ctor_get(v___y_5698_, 2);
v_inheritedTraceOptions_5924_ = lean_ctor_get(v___y_5698_, 13);
v_hasTrace_5925_ = lean_ctor_get_uint8(v_options_5923_, sizeof(void*)*1);
v___x_5926_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_5925_ == 0)
{
v___y_5928_ = v___y_5689_;
v___y_5929_ = v___y_5690_;
v___y_5930_ = v___y_5691_;
v___y_5931_ = v___y_5692_;
v___y_5932_ = v___y_5693_;
v___y_5933_ = v___y_5694_;
v___y_5934_ = v___y_5695_;
v___y_5935_ = v___y_5696_;
v___y_5936_ = v___y_5697_;
v___y_5937_ = v___y_5698_;
v___y_5938_ = v___y_5699_;
goto v___jp_5927_;
}
else
{
lean_object* v___x_6131_; uint8_t v___x_6132_; 
v___x_6131_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_6132_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5924_, v_options_5923_, v___x_6131_);
if (v___x_6132_ == 0)
{
v___y_5928_ = v___y_5689_;
v___y_5929_ = v___y_5690_;
v___y_5930_ = v___y_5691_;
v___y_5931_ = v___y_5692_;
v___y_5932_ = v___y_5693_;
v___y_5933_ = v___y_5694_;
v___y_5934_ = v___y_5695_;
v___y_5935_ = v___y_5696_;
v___y_5936_ = v___y_5697_;
v___y_5937_ = v___y_5698_;
v___y_5938_ = v___y_5699_;
goto v___jp_5927_;
}
else
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; 
v___x_6133_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_5913_);
v___x_6134_ = l_Lean_MessageData_ofExpr(v_a_5913_);
v___x_6135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6133_);
lean_ctor_set(v___x_6135_, 1, v___x_6134_);
v___x_6136_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5926_, v___x_6135_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
if (lean_obj_tag(v___x_6136_) == 0)
{
lean_dec_ref_known(v___x_6136_, 1);
v___y_5928_ = v___y_5689_;
v___y_5929_ = v___y_5690_;
v___y_5930_ = v___y_5691_;
v___y_5931_ = v___y_5692_;
v___y_5932_ = v___y_5693_;
v___y_5933_ = v___y_5694_;
v___y_5934_ = v___y_5695_;
v___y_5935_ = v___y_5696_;
v___y_5936_ = v___y_5697_;
v___y_5937_ = v___y_5698_;
v___y_5938_ = v___y_5699_;
goto v___jp_5927_;
}
else
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6144_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6137_ = lean_ctor_get(v___x_6136_, 0);
v_isSharedCheck_6144_ = !lean_is_exclusive(v___x_6136_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6139_ = v___x_6136_;
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v___x_6136_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6142_; 
if (v_isShared_6140_ == 0)
{
v___x_6142_ = v___x_6139_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_a_6137_);
v___x_6142_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
return v___x_6142_;
}
}
}
}
}
v___jp_5917_:
{
lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5921_; 
v___x_5918_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5918_, 0, v_a_5913_);
v___x_5919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5918_);
if (v_isShared_5916_ == 0)
{
lean_ctor_set(v___x_5915_, 0, v___x_5919_);
v___x_5921_ = v___x_5915_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5919_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
v___jp_5927_:
{
lean_object* v___x_5939_; 
lean_inc(v_goal_5687_);
v___x_5939_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_5687_, v_a_5913_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5939_) == 0)
{
lean_object* v_a_5940_; 
v_a_5940_ = lean_ctor_get(v___x_5939_, 0);
lean_inc(v_a_5940_);
lean_dec_ref_known(v___x_5939_, 1);
if (lean_obj_tag(v_a_5940_) == 1)
{
lean_object* v_val_5941_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_val_5941_ = lean_ctor_get(v_a_5940_, 0);
lean_inc(v_val_5941_);
lean_dec_ref_known(v_a_5940_, 1);
v_gs_5708_ = v_val_5941_;
goto v___jp_5707_;
}
else
{
lean_object* v___x_5942_; 
lean_dec(v_a_5940_);
lean_inc(v_a_5913_);
lean_inc(v_goal_5687_);
v___x_5942_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_5687_, v_a_5913_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5942_) == 0)
{
lean_object* v_a_5943_; 
v_a_5943_ = lean_ctor_get(v___x_5942_, 0);
lean_inc(v_a_5943_);
lean_dec_ref_known(v___x_5942_, 1);
if (lean_obj_tag(v_a_5943_) == 1)
{
lean_object* v_val_5944_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_val_5944_ = lean_ctor_get(v_a_5943_, 0);
lean_inc(v_val_5944_);
lean_dec_ref_known(v_a_5943_, 1);
v_g_5702_ = v_val_5944_;
goto v___jp_5701_;
}
else
{
lean_object* v___x_5945_; 
lean_dec(v_a_5943_);
lean_inc(v_goal_5687_);
v___x_5945_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_5687_, v_a_5913_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5945_) == 0)
{
lean_object* v_a_5946_; 
v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
lean_inc(v_a_5946_);
lean_dec_ref_known(v___x_5945_, 1);
if (lean_obj_tag(v_a_5946_) == 1)
{
lean_object* v_val_5947_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_val_5947_ = lean_ctor_get(v_a_5946_, 0);
lean_inc(v_val_5947_);
lean_dec_ref_known(v_a_5946_, 1);
v_g_5702_ = v_val_5947_;
goto v___jp_5701_;
}
else
{
lean_object* v___x_5948_; 
lean_dec(v_a_5946_);
lean_inc(v_a_5913_);
lean_inc(v_goal_5687_);
v___x_5948_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_5687_, v_a_5913_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5948_) == 0)
{
lean_object* v_a_5949_; 
v_a_5949_ = lean_ctor_get(v___x_5948_, 0);
lean_inc(v_a_5949_);
lean_dec_ref_known(v___x_5948_, 1);
if (lean_obj_tag(v_a_5949_) == 1)
{
lean_object* v_val_5950_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_val_5950_ = lean_ctor_get(v_a_5949_, 0);
lean_inc(v_val_5950_);
lean_dec_ref_known(v_a_5949_, 1);
v_g_5702_ = v_val_5950_;
goto v___jp_5701_;
}
else
{
lean_object* v___x_5951_; 
lean_dec(v_a_5949_);
lean_inc(v_a_5913_);
lean_inc(v_goal_5687_);
lean_inc_ref(v_scope_5688_);
v___x_5951_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_5688_, v_goal_5687_, v_a_5913_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5951_) == 0)
{
lean_object* v_a_5952_; 
v_a_5952_ = lean_ctor_get(v___x_5951_, 0);
lean_inc(v_a_5952_);
lean_dec_ref_known(v___x_5951_, 1);
if (lean_obj_tag(v_a_5952_) == 1)
{
lean_object* v_val_5953_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_val_5953_ = lean_ctor_get(v_a_5952_, 0);
lean_inc(v_val_5953_);
lean_dec_ref_known(v_a_5952_, 1);
v_gs_5708_ = v_val_5953_;
goto v___jp_5707_;
}
else
{
lean_object* v___x_5954_; uint8_t v___x_5955_; 
lean_dec(v_a_5952_);
lean_inc(v_a_5913_);
v___x_5954_ = l_Lean_Expr_cleanupAnnotations(v_a_5913_);
v___x_5955_ = l_Lean_Expr_isApp(v___x_5954_);
if (v___x_5955_ == 0)
{
lean_dec_ref(v___x_5954_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
goto v___jp_5917_;
}
else
{
lean_object* v_arg_5956_; lean_object* v___x_5957_; uint8_t v___x_5958_; 
v_arg_5956_ = lean_ctor_get(v___x_5954_, 1);
lean_inc_ref(v_arg_5956_);
v___x_5957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5954_);
v___x_5958_ = l_Lean_Expr_isApp(v___x_5957_);
if (v___x_5958_ == 0)
{
lean_dec_ref(v___x_5957_);
lean_dec_ref(v_arg_5956_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
goto v___jp_5917_;
}
else
{
lean_object* v_arg_5959_; lean_object* v___x_5960_; uint8_t v___x_5961_; 
v_arg_5959_ = lean_ctor_get(v___x_5957_, 1);
lean_inc_ref(v_arg_5959_);
v___x_5960_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5957_);
v___x_5961_ = l_Lean_Expr_isApp(v___x_5960_);
if (v___x_5961_ == 0)
{
lean_dec_ref(v___x_5960_);
lean_dec_ref(v_arg_5959_);
lean_dec_ref(v_arg_5956_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
goto v___jp_5917_;
}
else
{
lean_object* v_arg_5962_; lean_object* v___x_5963_; uint8_t v___x_5964_; 
v_arg_5962_ = lean_ctor_get(v___x_5960_, 1);
lean_inc_ref(v_arg_5962_);
v___x_5963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5960_);
v___x_5964_ = l_Lean_Expr_isApp(v___x_5963_);
if (v___x_5964_ == 0)
{
lean_dec_ref(v___x_5963_);
lean_dec_ref(v_arg_5962_);
lean_dec_ref(v_arg_5959_);
lean_dec_ref(v_arg_5956_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
goto v___jp_5917_;
}
else
{
lean_object* v_arg_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; uint8_t v___x_5968_; 
v_arg_5965_ = lean_ctor_get(v___x_5963_, 1);
lean_inc_ref(v_arg_5965_);
v___x_5966_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5963_);
v___x_5967_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5968_ = l_Lean_Expr_isConstOf(v___x_5966_, v___x_5967_);
lean_dec_ref(v___x_5966_);
if (v___x_5968_ == 0)
{
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec_ref(v_arg_5959_);
lean_dec_ref(v_arg_5956_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
goto v___jp_5917_;
}
else
{
lean_object* v___x_5969_; 
lean_del_object(v___x_5915_);
v___x_5969_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_5959_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5969_) == 0)
{
lean_object* v_a_5970_; lean_object* v___x_5971_; 
v_a_5970_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_a_5970_);
lean_dec_ref_known(v___x_5969_, 1);
v___x_5971_ = l_Lean_Meta_Sym_instantiateMVarsIfMVarAppS(v_arg_5956_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; lean_object* v___x_5973_; 
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
lean_inc(v_goal_5687_);
v___x_5973_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_5687_, v___y_5928_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5973_) == 0)
{
lean_object* v_a_5974_; 
v_a_5974_ = lean_ctor_get(v___x_5973_, 0);
lean_inc(v_a_5974_);
lean_dec_ref_known(v___x_5973_, 1);
if (lean_obj_tag(v_a_5974_) == 1)
{
lean_object* v_val_5975_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_val_5975_ = lean_ctor_get(v_a_5974_, 0);
lean_inc(v_val_5975_);
lean_dec_ref_known(v_a_5974_, 1);
v_gs_5708_ = v_val_5975_;
goto v___jp_5707_;
}
else
{
lean_object* v___x_5976_; 
lean_dec(v_a_5974_);
lean_inc(v_a_5913_);
lean_inc(v_a_5970_);
lean_inc(v_goal_5687_);
lean_inc_ref(v_scope_5688_);
v___x_5976_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_5688_, v_goal_5687_, v_arg_5965_, v_a_5970_, v_a_5913_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5976_) == 0)
{
lean_object* v_a_5977_; lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_6058_; 
v_a_5977_ = lean_ctor_get(v___x_5976_, 0);
v_isSharedCheck_6058_ = !lean_is_exclusive(v___x_5976_);
if (v_isSharedCheck_6058_ == 0)
{
v___x_5979_ = v___x_5976_;
v_isShared_5980_ = v_isSharedCheck_6058_;
goto v_resetjp_5978_;
}
else
{
lean_inc(v_a_5977_);
lean_dec(v___x_5976_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_6058_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
if (lean_obj_tag(v_a_5977_) == 1)
{
lean_object* v_val_5981_; lean_object* v_fst_5982_; lean_object* v_snd_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5993_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_val_5981_ = lean_ctor_get(v_a_5977_, 0);
lean_inc(v_val_5981_);
lean_dec_ref_known(v_a_5977_, 1);
v_fst_5982_ = lean_ctor_get(v_val_5981_, 0);
v_snd_5983_ = lean_ctor_get(v_val_5981_, 1);
v_isSharedCheck_5993_ = !lean_is_exclusive(v_val_5981_);
if (v_isSharedCheck_5993_ == 0)
{
v___x_5985_ = v_val_5981_;
v_isShared_5986_ = v_isSharedCheck_5993_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_snd_5983_);
lean_inc(v_fst_5982_);
lean_dec(v_val_5981_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5993_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5992_; 
v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5992_, 0, v_fst_5982_);
lean_ctor_set(v_reuseFailAlloc_5992_, 1, v_snd_5983_);
v___x_5988_ = v_reuseFailAlloc_5992_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
lean_object* v___x_5990_; 
if (v_isShared_5980_ == 0)
{
lean_ctor_set(v___x_5979_, 0, v___x_5988_);
v___x_5990_ = v___x_5979_;
goto v_reusejp_5989_;
}
else
{
lean_object* v_reuseFailAlloc_5991_; 
v_reuseFailAlloc_5991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5991_, 0, v___x_5988_);
v___x_5990_ = v_reuseFailAlloc_5991_;
goto v_reusejp_5989_;
}
v_reusejp_5989_:
{
return v___x_5990_;
}
}
}
}
else
{
lean_object* v___x_5994_; 
lean_del_object(v___x_5979_);
lean_dec(v_a_5977_);
lean_inc(v_goal_5687_);
v___x_5994_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_5688_, v_goal_5687_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5994_) == 0)
{
lean_object* v_a_5995_; lean_object* v___x_5996_; 
v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
lean_inc(v_a_5995_);
lean_dec_ref_known(v___x_5994_, 1);
lean_inc(v_a_5972_);
lean_inc(v_a_5970_);
lean_inc_ref(v_arg_5965_);
lean_inc(v_goal_5687_);
v___x_5996_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_5687_, v_a_5913_, v_arg_5965_, v_arg_5962_, v_a_5970_, v_a_5972_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5996_) == 0)
{
lean_object* v_a_5997_; 
v_a_5997_ = lean_ctor_get(v___x_5996_, 0);
lean_inc(v_a_5997_);
lean_dec_ref_known(v___x_5996_, 1);
if (lean_obj_tag(v_a_5997_) == 1)
{
lean_object* v_val_5998_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec(v_goal_5687_);
v_val_5998_ = lean_ctor_get(v_a_5997_, 0);
lean_inc(v_val_5998_);
lean_dec_ref_known(v_a_5997_, 1);
v___y_5718_ = v_a_5995_;
v_g_5719_ = v_val_5998_;
goto v___jp_5717_;
}
else
{
lean_object* v___x_5999_; 
lean_dec(v_a_5997_);
lean_inc(v_a_5972_);
lean_inc(v_goal_5687_);
v___x_5999_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_5687_, v_a_5972_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_5999_) == 0)
{
lean_object* v_a_6000_; 
v_a_6000_ = lean_ctor_get(v___x_5999_, 0);
lean_inc(v_a_6000_);
lean_dec_ref_known(v___x_5999_, 1);
if (lean_obj_tag(v_a_6000_) == 1)
{
lean_object* v_val_6001_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec(v_goal_5687_);
v_val_6001_ = lean_ctor_get(v_a_6000_, 0);
lean_inc(v_val_6001_);
lean_dec_ref_known(v_a_6000_, 1);
v___y_5725_ = v_a_5995_;
v_gs_5726_ = v_val_6001_;
goto v___jp_5724_;
}
else
{
lean_object* v___x_6002_; 
lean_dec(v_a_6000_);
lean_inc(v_a_5972_);
lean_inc(v_a_5970_);
lean_inc(v_goal_5687_);
lean_inc(v_a_5995_);
v___x_6002_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_a_5995_, v_goal_5687_, v_arg_5965_, v_a_5970_, v_a_5972_, v___y_5928_, v___y_5929_, v___y_5930_, v___y_5931_, v___y_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
lean_dec_ref(v_arg_5965_);
if (lean_obj_tag(v___x_6002_) == 0)
{
lean_object* v_a_6003_; 
v_a_6003_ = lean_ctor_get(v___x_6002_, 0);
lean_inc(v_a_6003_);
lean_dec_ref_known(v___x_6002_, 1);
if (lean_obj_tag(v_a_6003_) == 1)
{
lean_object* v_val_6004_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec(v_goal_5687_);
v_val_6004_ = lean_ctor_get(v_a_6003_, 0);
lean_inc(v_val_6004_);
lean_dec_ref_known(v_a_6003_, 1);
v___y_5725_ = v_a_5995_;
v_gs_5726_ = v_val_6004_;
goto v___jp_5724_;
}
else
{
lean_object* v___x_6005_; 
lean_dec(v_a_6003_);
lean_inc(v_a_5972_);
v___x_6005_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(v_a_5972_);
if (lean_obj_tag(v___x_6005_) == 1)
{
lean_object* v_options_6006_; uint8_t v_hasTrace_6007_; 
v_options_6006_ = lean_ctor_get(v___y_5937_, 2);
v_hasTrace_6007_ = lean_ctor_get_uint8(v_options_6006_, sizeof(void*)*1);
if (v_hasTrace_6007_ == 0)
{
lean_object* v_val_6008_; 
v_val_6008_ = lean_ctor_get(v___x_6005_, 0);
lean_inc(v_val_6008_);
lean_dec_ref_known(v___x_6005_, 1);
v___y_5779_ = v_a_5970_;
v___y_5780_ = v_val_6008_;
v___y_5781_ = v_a_5995_;
v___y_5782_ = v_a_5972_;
v___y_5783_ = v___y_5928_;
v___y_5784_ = v___y_5929_;
v___y_5785_ = v___y_5930_;
v___y_5786_ = v___y_5931_;
v___y_5787_ = v___y_5932_;
v___y_5788_ = v___y_5933_;
v___y_5789_ = v___y_5934_;
v___y_5790_ = v___y_5935_;
v___y_5791_ = v___y_5936_;
v___y_5792_ = v___y_5937_;
v___y_5793_ = v___y_5938_;
goto v___jp_5778_;
}
else
{
lean_object* v_val_6009_; lean_object* v_inheritedTraceOptions_6010_; lean_object* v___x_6011_; uint8_t v___x_6012_; 
v_val_6009_ = lean_ctor_get(v___x_6005_, 0);
lean_inc(v_val_6009_);
lean_dec_ref_known(v___x_6005_, 1);
v_inheritedTraceOptions_6010_ = lean_ctor_get(v___y_5937_, 13);
v___x_6011_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_6012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6010_, v_options_6006_, v___x_6011_);
if (v___x_6012_ == 0)
{
v___y_5779_ = v_a_5970_;
v___y_5780_ = v_val_6009_;
v___y_5781_ = v_a_5995_;
v___y_5782_ = v_a_5972_;
v___y_5783_ = v___y_5928_;
v___y_5784_ = v___y_5929_;
v___y_5785_ = v___y_5930_;
v___y_5786_ = v___y_5931_;
v___y_5787_ = v___y_5932_;
v___y_5788_ = v___y_5933_;
v___y_5789_ = v___y_5934_;
v___y_5790_ = v___y_5935_;
v___y_5791_ = v___y_5936_;
v___y_5792_ = v___y_5937_;
v___y_5793_ = v___y_5938_;
goto v___jp_5778_;
}
else
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; 
v___x_6013_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5);
v___x_6014_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_val_6009_);
v___x_6015_ = l_Lean_MessageData_ofExpr(v___x_6014_);
v___x_6016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6013_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
v___x_6017_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5926_, v___x_6016_, v___y_5935_, v___y_5936_, v___y_5937_, v___y_5938_);
if (lean_obj_tag(v___x_6017_) == 0)
{
lean_dec_ref_known(v___x_6017_, 1);
v___y_5779_ = v_a_5970_;
v___y_5780_ = v_val_6009_;
v___y_5781_ = v_a_5995_;
v___y_5782_ = v_a_5972_;
v___y_5783_ = v___y_5928_;
v___y_5784_ = v___y_5929_;
v___y_5785_ = v___y_5930_;
v___y_5786_ = v___y_5931_;
v___y_5787_ = v___y_5932_;
v___y_5788_ = v___y_5933_;
v___y_5789_ = v___y_5934_;
v___y_5790_ = v___y_5935_;
v___y_5791_ = v___y_5936_;
v___y_5792_ = v___y_5937_;
v___y_5793_ = v___y_5938_;
goto v___jp_5778_;
}
else
{
lean_object* v_a_6018_; lean_object* v___x_6020_; uint8_t v_isShared_6021_; uint8_t v_isSharedCheck_6025_; 
lean_dec(v_val_6009_);
lean_dec(v_a_5995_);
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec(v_goal_5687_);
v_a_6018_ = lean_ctor_get(v___x_6017_, 0);
v_isSharedCheck_6025_ = !lean_is_exclusive(v___x_6017_);
if (v_isSharedCheck_6025_ == 0)
{
v___x_6020_ = v___x_6017_;
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
else
{
lean_inc(v_a_6018_);
lean_dec(v___x_6017_);
v___x_6020_ = lean_box(0);
v_isShared_6021_ = v_isSharedCheck_6025_;
goto v_resetjp_6019_;
}
v_resetjp_6019_:
{
lean_object* v___x_6023_; 
if (v_isShared_6021_ == 0)
{
v___x_6023_ = v___x_6020_;
goto v_reusejp_6022_;
}
else
{
lean_object* v_reuseFailAlloc_6024_; 
v_reuseFailAlloc_6024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6024_, 0, v_a_6018_);
v___x_6023_ = v_reuseFailAlloc_6024_;
goto v_reusejp_6022_;
}
v_reusejp_6022_:
{
return v___x_6023_;
}
}
}
}
}
}
else
{
lean_dec(v___x_6005_);
lean_dec(v_a_5995_);
lean_dec(v_goal_5687_);
v___y_5712_ = v_a_5970_;
v___y_5713_ = v_a_5972_;
goto v___jp_5711_;
}
}
}
else
{
lean_object* v_a_6026_; lean_object* v___x_6028_; uint8_t v_isShared_6029_; uint8_t v_isSharedCheck_6033_; 
lean_dec(v_a_5995_);
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec(v_goal_5687_);
v_a_6026_ = lean_ctor_get(v___x_6002_, 0);
v_isSharedCheck_6033_ = !lean_is_exclusive(v___x_6002_);
if (v_isSharedCheck_6033_ == 0)
{
v___x_6028_ = v___x_6002_;
v_isShared_6029_ = v_isSharedCheck_6033_;
goto v_resetjp_6027_;
}
else
{
lean_inc(v_a_6026_);
lean_dec(v___x_6002_);
v___x_6028_ = lean_box(0);
v_isShared_6029_ = v_isSharedCheck_6033_;
goto v_resetjp_6027_;
}
v_resetjp_6027_:
{
lean_object* v___x_6031_; 
if (v_isShared_6029_ == 0)
{
v___x_6031_ = v___x_6028_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6032_; 
v_reuseFailAlloc_6032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6032_, 0, v_a_6026_);
v___x_6031_ = v_reuseFailAlloc_6032_;
goto v_reusejp_6030_;
}
v_reusejp_6030_:
{
return v___x_6031_;
}
}
}
}
}
else
{
lean_object* v_a_6034_; lean_object* v___x_6036_; uint8_t v_isShared_6037_; uint8_t v_isSharedCheck_6041_; 
lean_dec(v_a_5995_);
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec(v_goal_5687_);
v_a_6034_ = lean_ctor_get(v___x_5999_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v___x_5999_);
if (v_isSharedCheck_6041_ == 0)
{
v___x_6036_ = v___x_5999_;
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
else
{
lean_inc(v_a_6034_);
lean_dec(v___x_5999_);
v___x_6036_ = lean_box(0);
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
v_resetjp_6035_:
{
lean_object* v___x_6039_; 
if (v_isShared_6037_ == 0)
{
v___x_6039_ = v___x_6036_;
goto v_reusejp_6038_;
}
else
{
lean_object* v_reuseFailAlloc_6040_; 
v_reuseFailAlloc_6040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6040_, 0, v_a_6034_);
v___x_6039_ = v_reuseFailAlloc_6040_;
goto v_reusejp_6038_;
}
v_reusejp_6038_:
{
return v___x_6039_;
}
}
}
}
}
else
{
lean_object* v_a_6042_; lean_object* v___x_6044_; uint8_t v_isShared_6045_; uint8_t v_isSharedCheck_6049_; 
lean_dec(v_a_5995_);
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec(v_goal_5687_);
v_a_6042_ = lean_ctor_get(v___x_5996_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_5996_);
if (v_isSharedCheck_6049_ == 0)
{
v___x_6044_ = v___x_5996_;
v_isShared_6045_ = v_isSharedCheck_6049_;
goto v_resetjp_6043_;
}
else
{
lean_inc(v_a_6042_);
lean_dec(v___x_5996_);
v___x_6044_ = lean_box(0);
v_isShared_6045_ = v_isSharedCheck_6049_;
goto v_resetjp_6043_;
}
v_resetjp_6043_:
{
lean_object* v___x_6047_; 
if (v_isShared_6045_ == 0)
{
v___x_6047_ = v___x_6044_;
goto v_reusejp_6046_;
}
else
{
lean_object* v_reuseFailAlloc_6048_; 
v_reuseFailAlloc_6048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_a_6042_);
v___x_6047_ = v_reuseFailAlloc_6048_;
goto v_reusejp_6046_;
}
v_reusejp_6046_:
{
return v___x_6047_;
}
}
}
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec(v_a_5913_);
lean_dec(v_goal_5687_);
v_a_6050_ = lean_ctor_get(v___x_5994_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_5994_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_5994_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_5994_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
}
}
}
}
}
}
else
{
lean_object* v_a_6059_; lean_object* v___x_6061_; uint8_t v_isShared_6062_; uint8_t v_isSharedCheck_6066_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6059_ = lean_ctor_get(v___x_5976_, 0);
v_isSharedCheck_6066_ = !lean_is_exclusive(v___x_5976_);
if (v_isSharedCheck_6066_ == 0)
{
v___x_6061_ = v___x_5976_;
v_isShared_6062_ = v_isSharedCheck_6066_;
goto v_resetjp_6060_;
}
else
{
lean_inc(v_a_6059_);
lean_dec(v___x_5976_);
v___x_6061_ = lean_box(0);
v_isShared_6062_ = v_isSharedCheck_6066_;
goto v_resetjp_6060_;
}
v_resetjp_6060_:
{
lean_object* v___x_6064_; 
if (v_isShared_6062_ == 0)
{
v___x_6064_ = v___x_6061_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
v___x_6064_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
return v___x_6064_;
}
}
}
}
}
else
{
lean_object* v_a_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6074_; 
lean_dec(v_a_5972_);
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6067_ = lean_ctor_get(v___x_5973_, 0);
v_isSharedCheck_6074_ = !lean_is_exclusive(v___x_5973_);
if (v_isSharedCheck_6074_ == 0)
{
v___x_6069_ = v___x_5973_;
v_isShared_6070_ = v_isSharedCheck_6074_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_a_6067_);
lean_dec(v___x_5973_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6074_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6072_; 
if (v_isShared_6070_ == 0)
{
v___x_6072_ = v___x_6069_;
goto v_reusejp_6071_;
}
else
{
lean_object* v_reuseFailAlloc_6073_; 
v_reuseFailAlloc_6073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6073_, 0, v_a_6067_);
v___x_6072_ = v_reuseFailAlloc_6073_;
goto v_reusejp_6071_;
}
v_reusejp_6071_:
{
return v___x_6072_;
}
}
}
}
else
{
lean_object* v_a_6075_; lean_object* v___x_6077_; uint8_t v_isShared_6078_; uint8_t v_isSharedCheck_6082_; 
lean_dec(v_a_5970_);
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6075_ = lean_ctor_get(v___x_5971_, 0);
v_isSharedCheck_6082_ = !lean_is_exclusive(v___x_5971_);
if (v_isSharedCheck_6082_ == 0)
{
v___x_6077_ = v___x_5971_;
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
else
{
lean_inc(v_a_6075_);
lean_dec(v___x_5971_);
v___x_6077_ = lean_box(0);
v_isShared_6078_ = v_isSharedCheck_6082_;
goto v_resetjp_6076_;
}
v_resetjp_6076_:
{
lean_object* v___x_6080_; 
if (v_isShared_6078_ == 0)
{
v___x_6080_ = v___x_6077_;
goto v_reusejp_6079_;
}
else
{
lean_object* v_reuseFailAlloc_6081_; 
v_reuseFailAlloc_6081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6081_, 0, v_a_6075_);
v___x_6080_ = v_reuseFailAlloc_6081_;
goto v_reusejp_6079_;
}
v_reusejp_6079_:
{
return v___x_6080_;
}
}
}
}
else
{
lean_object* v_a_6083_; lean_object* v___x_6085_; uint8_t v_isShared_6086_; uint8_t v_isSharedCheck_6090_; 
lean_dec_ref(v_arg_5965_);
lean_dec_ref(v_arg_5962_);
lean_dec_ref(v_arg_5956_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6083_ = lean_ctor_get(v___x_5969_, 0);
v_isSharedCheck_6090_ = !lean_is_exclusive(v___x_5969_);
if (v_isSharedCheck_6090_ == 0)
{
v___x_6085_ = v___x_5969_;
v_isShared_6086_ = v_isSharedCheck_6090_;
goto v_resetjp_6084_;
}
else
{
lean_inc(v_a_6083_);
lean_dec(v___x_5969_);
v___x_6085_ = lean_box(0);
v_isShared_6086_ = v_isSharedCheck_6090_;
goto v_resetjp_6084_;
}
v_resetjp_6084_:
{
lean_object* v___x_6088_; 
if (v_isShared_6086_ == 0)
{
v___x_6088_ = v___x_6085_;
goto v_reusejp_6087_;
}
else
{
lean_object* v_reuseFailAlloc_6089_; 
v_reuseFailAlloc_6089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6089_, 0, v_a_6083_);
v___x_6088_ = v_reuseFailAlloc_6089_;
goto v_reusejp_6087_;
}
v_reusejp_6087_:
{
return v___x_6088_;
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
lean_object* v_a_6091_; lean_object* v___x_6093_; uint8_t v_isShared_6094_; uint8_t v_isSharedCheck_6098_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6091_ = lean_ctor_get(v___x_5951_, 0);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_5951_);
if (v_isSharedCheck_6098_ == 0)
{
v___x_6093_ = v___x_5951_;
v_isShared_6094_ = v_isSharedCheck_6098_;
goto v_resetjp_6092_;
}
else
{
lean_inc(v_a_6091_);
lean_dec(v___x_5951_);
v___x_6093_ = lean_box(0);
v_isShared_6094_ = v_isSharedCheck_6098_;
goto v_resetjp_6092_;
}
v_resetjp_6092_:
{
lean_object* v___x_6096_; 
if (v_isShared_6094_ == 0)
{
v___x_6096_ = v___x_6093_;
goto v_reusejp_6095_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_a_6091_);
v___x_6096_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6095_;
}
v_reusejp_6095_:
{
return v___x_6096_;
}
}
}
}
}
else
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6106_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6099_ = lean_ctor_get(v___x_5948_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_5948_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6101_ = v___x_5948_;
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v___x_5948_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6104_; 
if (v_isShared_6102_ == 0)
{
v___x_6104_ = v___x_6101_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
}
else
{
lean_object* v_a_6107_; lean_object* v___x_6109_; uint8_t v_isShared_6110_; uint8_t v_isSharedCheck_6114_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6107_ = lean_ctor_get(v___x_5945_, 0);
v_isSharedCheck_6114_ = !lean_is_exclusive(v___x_5945_);
if (v_isSharedCheck_6114_ == 0)
{
v___x_6109_ = v___x_5945_;
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
else
{
lean_inc(v_a_6107_);
lean_dec(v___x_5945_);
v___x_6109_ = lean_box(0);
v_isShared_6110_ = v_isSharedCheck_6114_;
goto v_resetjp_6108_;
}
v_resetjp_6108_:
{
lean_object* v___x_6112_; 
if (v_isShared_6110_ == 0)
{
v___x_6112_ = v___x_6109_;
goto v_reusejp_6111_;
}
else
{
lean_object* v_reuseFailAlloc_6113_; 
v_reuseFailAlloc_6113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6113_, 0, v_a_6107_);
v___x_6112_ = v_reuseFailAlloc_6113_;
goto v_reusejp_6111_;
}
v_reusejp_6111_:
{
return v___x_6112_;
}
}
}
}
}
else
{
lean_object* v_a_6115_; lean_object* v___x_6117_; uint8_t v_isShared_6118_; uint8_t v_isSharedCheck_6122_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6115_ = lean_ctor_get(v___x_5942_, 0);
v_isSharedCheck_6122_ = !lean_is_exclusive(v___x_5942_);
if (v_isSharedCheck_6122_ == 0)
{
v___x_6117_ = v___x_5942_;
v_isShared_6118_ = v_isSharedCheck_6122_;
goto v_resetjp_6116_;
}
else
{
lean_inc(v_a_6115_);
lean_dec(v___x_5942_);
v___x_6117_ = lean_box(0);
v_isShared_6118_ = v_isSharedCheck_6122_;
goto v_resetjp_6116_;
}
v_resetjp_6116_:
{
lean_object* v___x_6120_; 
if (v_isShared_6118_ == 0)
{
v___x_6120_ = v___x_6117_;
goto v_reusejp_6119_;
}
else
{
lean_object* v_reuseFailAlloc_6121_; 
v_reuseFailAlloc_6121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6121_, 0, v_a_6115_);
v___x_6120_ = v_reuseFailAlloc_6121_;
goto v_reusejp_6119_;
}
v_reusejp_6119_:
{
return v___x_6120_;
}
}
}
}
}
else
{
lean_object* v_a_6123_; lean_object* v___x_6125_; uint8_t v_isShared_6126_; uint8_t v_isSharedCheck_6130_; 
lean_del_object(v___x_5915_);
lean_dec(v_a_5913_);
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6123_ = lean_ctor_get(v___x_5939_, 0);
v_isSharedCheck_6130_ = !lean_is_exclusive(v___x_5939_);
if (v_isSharedCheck_6130_ == 0)
{
v___x_6125_ = v___x_5939_;
v_isShared_6126_ = v_isSharedCheck_6130_;
goto v_resetjp_6124_;
}
else
{
lean_inc(v_a_6123_);
lean_dec(v___x_5939_);
v___x_6125_ = lean_box(0);
v_isShared_6126_ = v_isSharedCheck_6130_;
goto v_resetjp_6124_;
}
v_resetjp_6124_:
{
lean_object* v___x_6128_; 
if (v_isShared_6126_ == 0)
{
v___x_6128_ = v___x_6125_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v_a_6123_);
v___x_6128_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
return v___x_6128_;
}
}
}
}
}
}
else
{
lean_object* v_a_6146_; lean_object* v___x_6148_; uint8_t v_isShared_6149_; uint8_t v_isSharedCheck_6153_; 
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6146_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_6153_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_6153_ == 0)
{
v___x_6148_ = v___x_5912_;
v_isShared_6149_ = v_isSharedCheck_6153_;
goto v_resetjp_6147_;
}
else
{
lean_inc(v_a_6146_);
lean_dec(v___x_5912_);
v___x_6148_ = lean_box(0);
v_isShared_6149_ = v_isSharedCheck_6153_;
goto v_resetjp_6147_;
}
v_resetjp_6147_:
{
lean_object* v___x_6151_; 
if (v_isShared_6149_ == 0)
{
v___x_6151_ = v___x_6148_;
goto v_reusejp_6150_;
}
else
{
lean_object* v_reuseFailAlloc_6152_; 
v_reuseFailAlloc_6152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6152_, 0, v_a_6146_);
v___x_6151_ = v_reuseFailAlloc_6152_;
goto v_reusejp_6150_;
}
v_reusejp_6150_:
{
return v___x_6151_;
}
}
}
}
else
{
lean_object* v___x_6154_; lean_object* v___x_6156_; 
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v___x_6154_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
if (v_isShared_5910_ == 0)
{
lean_ctor_set(v___x_5909_, 0, v___x_6154_);
v___x_6156_ = v___x_5909_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v___x_6154_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
}
else
{
lean_object* v_a_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6166_; 
lean_dec_ref(v_scope_5688_);
lean_dec(v_goal_5687_);
v_a_6159_ = lean_ctor_get(v___x_5906_, 0);
v_isSharedCheck_6166_ = !lean_is_exclusive(v___x_5906_);
if (v_isSharedCheck_6166_ == 0)
{
v___x_6161_ = v___x_5906_;
v_isShared_6162_ = v_isSharedCheck_6166_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_a_6159_);
lean_dec(v___x_5906_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6166_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6164_; 
if (v_isShared_6162_ == 0)
{
v___x_6164_ = v___x_6161_;
goto v_reusejp_6163_;
}
else
{
lean_object* v_reuseFailAlloc_6165_; 
v_reuseFailAlloc_6165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6165_, 0, v_a_6159_);
v___x_6164_ = v_reuseFailAlloc_6165_;
goto v_reusejp_6163_;
}
v_reusejp_6163_:
{
return v___x_6164_;
}
}
}
v___jp_5701_:
{
lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5703_ = lean_box(0);
v___x_5704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5704_, 0, v_g_5702_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
v___x_5705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5705_, 0, v_scope_5688_);
lean_ctor_set(v___x_5705_, 1, v___x_5704_);
v___x_5706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5706_, 0, v___x_5705_);
return v___x_5706_;
}
v___jp_5707_:
{
lean_object* v___x_5709_; lean_object* v___x_5710_; 
v___x_5709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5709_, 0, v_scope_5688_);
lean_ctor_set(v___x_5709_, 1, v_gs_5708_);
v___x_5710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5710_, 0, v___x_5709_);
return v___x_5710_;
}
v___jp_5711_:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; 
v___x_5714_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5714_, 0, v___y_5712_);
lean_ctor_set(v___x_5714_, 1, v___y_5713_);
v___x_5715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
v___x_5716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5716_, 0, v___x_5715_);
return v___x_5716_;
}
v___jp_5717_:
{
lean_object* v___x_5720_; lean_object* v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
v___x_5720_ = lean_box(0);
v___x_5721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5721_, 0, v_g_5719_);
lean_ctor_set(v___x_5721_, 1, v___x_5720_);
v___x_5722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5722_, 0, v___y_5718_);
lean_ctor_set(v___x_5722_, 1, v___x_5721_);
v___x_5723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
return v___x_5723_;
}
v___jp_5724_:
{
lean_object* v___x_5727_; lean_object* v___x_5728_; 
v___x_5727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5727_, 0, v___y_5725_);
lean_ctor_set(v___x_5727_, 1, v_gs_5726_);
v___x_5728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5728_, 0, v___x_5727_);
return v___x_5728_;
}
v___jp_5729_:
{
lean_object* v___x_5733_; 
v___x_5733_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5732_);
if (lean_obj_tag(v___x_5733_) == 0)
{
lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5743_; 
v_isSharedCheck_5743_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5743_ == 0)
{
lean_object* v_unused_5744_; 
v_unused_5744_ = lean_ctor_get(v___x_5733_, 0);
lean_dec(v_unused_5744_);
v___x_5735_ = v___x_5733_;
v_isShared_5736_ = v_isSharedCheck_5743_;
goto v_resetjp_5734_;
}
else
{
lean_dec(v___x_5733_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5743_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5741_; 
v___x_5737_ = lean_box(0);
v___x_5738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5738_, 0, v_g_5731_);
lean_ctor_set(v___x_5738_, 1, v___x_5737_);
v___x_5739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5739_, 0, v___y_5730_);
lean_ctor_set(v___x_5739_, 1, v___x_5738_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 0, v___x_5739_);
v___x_5741_ = v___x_5735_;
goto v_reusejp_5740_;
}
else
{
lean_object* v_reuseFailAlloc_5742_; 
v_reuseFailAlloc_5742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5742_, 0, v___x_5739_);
v___x_5741_ = v_reuseFailAlloc_5742_;
goto v_reusejp_5740_;
}
v_reusejp_5740_:
{
return v___x_5741_;
}
}
}
else
{
lean_object* v_a_5745_; lean_object* v___x_5747_; uint8_t v_isShared_5748_; uint8_t v_isSharedCheck_5752_; 
lean_dec(v_g_5731_);
lean_dec_ref(v___y_5730_);
v_a_5745_ = lean_ctor_get(v___x_5733_, 0);
v_isSharedCheck_5752_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5752_ == 0)
{
v___x_5747_ = v___x_5733_;
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
else
{
lean_inc(v_a_5745_);
lean_dec(v___x_5733_);
v___x_5747_ = lean_box(0);
v_isShared_5748_ = v_isSharedCheck_5752_;
goto v_resetjp_5746_;
}
v_resetjp_5746_:
{
lean_object* v___x_5750_; 
if (v_isShared_5748_ == 0)
{
v___x_5750_ = v___x_5747_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5751_; 
v_reuseFailAlloc_5751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
v___x_5750_ = v_reuseFailAlloc_5751_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
return v___x_5750_;
}
}
}
}
v___jp_5753_:
{
lean_object* v___x_5768_; 
v___x_5768_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5759_);
if (lean_obj_tag(v___x_5768_) == 0)
{
lean_object* v___x_5769_; 
lean_dec_ref_known(v___x_5768_, 1);
v___x_5769_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrameOrSpec(v___y_5764_, v_goal_5687_, v___y_5754_, v___y_5763_, v___y_5767_, v___y_5759_, v___y_5762_, v___y_5765_, v___y_5756_, v___y_5755_, v___y_5757_, v___y_5760_, v___y_5766_, v___y_5758_, v___y_5761_);
return v___x_5769_;
}
else
{
lean_object* v_a_5770_; lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5777_; 
lean_dec_ref(v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec_ref(v___y_5754_);
lean_dec(v_goal_5687_);
v_a_5770_ = lean_ctor_get(v___x_5768_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5768_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5772_ = v___x_5768_;
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
else
{
lean_inc(v_a_5770_);
lean_dec(v___x_5768_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___x_5775_; 
if (v_isShared_5773_ == 0)
{
v___x_5775_ = v___x_5772_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_a_5770_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
}
v___jp_5778_:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; 
lean_dec_ref(v___y_5782_);
v___x_5794_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v___y_5780_);
lean_inc_ref(v___x_5794_);
v___x_5795_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v___x_5794_, v___y_5783_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5897_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5897_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5897_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_5897_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5897_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
uint8_t v___x_5800_; 
v___x_5800_ = lean_unbox(v_a_5796_);
lean_dec(v_a_5796_);
if (v___x_5800_ == 0)
{
lean_object* v___x_5801_; 
lean_del_object(v___x_5798_);
lean_inc_ref(v___y_5780_);
lean_inc(v_goal_5687_);
v___x_5801_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_5687_, v___y_5780_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
lean_inc(v_a_5802_);
lean_dec_ref_known(v___x_5801_, 1);
if (lean_obj_tag(v_a_5802_) == 1)
{
lean_object* v_val_5803_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_val_5803_ = lean_ctor_get(v_a_5802_, 0);
lean_inc(v_val_5803_);
lean_dec_ref_known(v_a_5802_, 1);
v___y_5718_ = v___y_5781_;
v_g_5719_ = v_val_5803_;
goto v___jp_5717_;
}
else
{
lean_object* v___x_5804_; 
lean_dec(v_a_5802_);
lean_inc_ref(v___y_5780_);
lean_inc(v_goal_5687_);
v___x_5804_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_5687_, v___y_5780_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5804_) == 0)
{
lean_object* v_a_5805_; 
v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
lean_inc(v_a_5805_);
lean_dec_ref_known(v___x_5804_, 1);
if (lean_obj_tag(v_a_5805_) == 1)
{
lean_object* v_val_5806_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_val_5806_ = lean_ctor_get(v_a_5805_, 0);
lean_inc(v_val_5806_);
lean_dec_ref_known(v_a_5805_, 1);
v___y_5730_ = v___y_5781_;
v_g_5731_ = v_val_5806_;
v___y_5732_ = v___y_5784_;
goto v___jp_5729_;
}
else
{
lean_object* v___x_5807_; 
lean_dec(v_a_5805_);
lean_inc_ref(v___y_5780_);
lean_inc(v_goal_5687_);
v___x_5807_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_5687_, v___y_5780_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5807_) == 0)
{
lean_object* v_a_5808_; 
v_a_5808_ = lean_ctor_get(v___x_5807_, 0);
lean_inc(v_a_5808_);
lean_dec_ref_known(v___x_5807_, 1);
if (lean_obj_tag(v_a_5808_) == 1)
{
lean_object* v_val_5809_; lean_object* v___x_5810_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_val_5809_ = lean_ctor_get(v_a_5808_, 0);
lean_inc(v_val_5809_);
lean_dec_ref_known(v_a_5808_, 1);
v___x_5810_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5784_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v___x_5812_; uint8_t v_isShared_5813_; uint8_t v_isSharedCheck_5818_; 
v_isSharedCheck_5818_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5818_ == 0)
{
lean_object* v_unused_5819_; 
v_unused_5819_ = lean_ctor_get(v___x_5810_, 0);
lean_dec(v_unused_5819_);
v___x_5812_ = v___x_5810_;
v_isShared_5813_ = v_isSharedCheck_5818_;
goto v_resetjp_5811_;
}
else
{
lean_dec(v___x_5810_);
v___x_5812_ = lean_box(0);
v_isShared_5813_ = v_isSharedCheck_5818_;
goto v_resetjp_5811_;
}
v_resetjp_5811_:
{
lean_object* v___x_5814_; lean_object* v___x_5816_; 
v___x_5814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5814_, 0, v___y_5781_);
lean_ctor_set(v___x_5814_, 1, v_val_5809_);
if (v_isShared_5813_ == 0)
{
lean_ctor_set(v___x_5812_, 0, v___x_5814_);
v___x_5816_ = v___x_5812_;
goto v_reusejp_5815_;
}
else
{
lean_object* v_reuseFailAlloc_5817_; 
v_reuseFailAlloc_5817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5817_, 0, v___x_5814_);
v___x_5816_ = v_reuseFailAlloc_5817_;
goto v_reusejp_5815_;
}
v_reusejp_5815_:
{
return v___x_5816_;
}
}
}
else
{
lean_object* v_a_5820_; lean_object* v___x_5822_; uint8_t v_isShared_5823_; uint8_t v_isSharedCheck_5827_; 
lean_dec(v_val_5809_);
lean_dec_ref(v___y_5781_);
v_a_5820_ = lean_ctor_get(v___x_5810_, 0);
v_isSharedCheck_5827_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5827_ == 0)
{
v___x_5822_ = v___x_5810_;
v_isShared_5823_ = v_isSharedCheck_5827_;
goto v_resetjp_5821_;
}
else
{
lean_inc(v_a_5820_);
lean_dec(v___x_5810_);
v___x_5822_ = lean_box(0);
v_isShared_5823_ = v_isSharedCheck_5827_;
goto v_resetjp_5821_;
}
v_resetjp_5821_:
{
lean_object* v___x_5825_; 
if (v_isShared_5823_ == 0)
{
v___x_5825_ = v___x_5822_;
goto v_reusejp_5824_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v_a_5820_);
v___x_5825_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5824_;
}
v_reusejp_5824_:
{
return v___x_5825_;
}
}
}
}
else
{
lean_object* v___x_5828_; 
lean_dec(v_a_5808_);
lean_inc_ref(v___y_5780_);
lean_inc(v_goal_5687_);
v___x_5828_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_5687_, v___y_5780_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5828_) == 0)
{
lean_object* v_a_5829_; 
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5829_);
lean_dec_ref_known(v___x_5828_, 1);
if (lean_obj_tag(v_a_5829_) == 1)
{
lean_object* v_val_5830_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_val_5830_ = lean_ctor_get(v_a_5829_, 0);
lean_inc(v_val_5830_);
lean_dec_ref_known(v_a_5829_, 1);
v___y_5730_ = v___y_5781_;
v_g_5731_ = v_val_5830_;
v___y_5732_ = v___y_5784_;
goto v___jp_5729_;
}
else
{
lean_object* v___x_5831_; 
lean_dec(v_a_5829_);
lean_inc_ref(v___y_5780_);
lean_inc(v_goal_5687_);
v___x_5831_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_5687_, v___y_5780_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
lean_inc(v_a_5832_);
lean_dec_ref_known(v___x_5831_, 1);
if (lean_obj_tag(v_a_5832_) == 1)
{
lean_object* v_val_5833_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_val_5833_ = lean_ctor_get(v_a_5832_, 0);
lean_inc(v_val_5833_);
lean_dec_ref_known(v_a_5832_, 1);
v___y_5730_ = v___y_5781_;
v_g_5731_ = v_val_5833_;
v___y_5732_ = v___y_5784_;
goto v___jp_5729_;
}
else
{
lean_object* v___x_5834_; uint8_t v___x_5835_; 
lean_dec(v_a_5832_);
v___x_5834_ = l_Lean_Expr_getAppFn(v___x_5794_);
v___x_5835_ = l_Lean_Expr_isConst(v___x_5834_);
if (v___x_5835_ == 0)
{
uint8_t v___x_5836_; 
v___x_5836_ = l_Lean_Expr_isFVar(v___x_5834_);
lean_dec_ref(v___x_5834_);
if (v___x_5836_ == 0)
{
lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v_a_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5850_; 
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v___x_5837_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v___x_5838_ = l_Lean_MessageData_ofExpr(v___x_5794_);
v___x_5839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5839_, 0, v___x_5837_);
lean_ctor_set(v___x_5839_, 1, v___x_5838_);
v___x_5840_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3);
v___x_5841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5841_, 0, v___x_5839_);
lean_ctor_set(v___x_5841_, 1, v___x_5840_);
v___x_5842_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5841_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_);
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
v_isSharedCheck_5850_ = !lean_is_exclusive(v___x_5842_);
if (v_isSharedCheck_5850_ == 0)
{
v___x_5845_ = v___x_5842_;
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_a_5843_);
lean_dec(v___x_5842_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5848_; 
if (v_isShared_5846_ == 0)
{
v___x_5848_ = v___x_5845_;
goto v_reusejp_5847_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
v___x_5848_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5847_;
}
v_reusejp_5847_:
{
return v___x_5848_;
}
}
}
else
{
lean_dec_ref(v___x_5794_);
v___y_5754_ = v___y_5779_;
v___y_5755_ = v___y_5788_;
v___y_5756_ = v___y_5787_;
v___y_5757_ = v___y_5789_;
v___y_5758_ = v___y_5792_;
v___y_5759_ = v___y_5784_;
v___y_5760_ = v___y_5790_;
v___y_5761_ = v___y_5793_;
v___y_5762_ = v___y_5785_;
v___y_5763_ = v___y_5780_;
v___y_5764_ = v___y_5781_;
v___y_5765_ = v___y_5786_;
v___y_5766_ = v___y_5791_;
v___y_5767_ = v___y_5783_;
goto v___jp_5753_;
}
}
else
{
lean_dec_ref(v___x_5834_);
lean_dec_ref(v___x_5794_);
v___y_5754_ = v___y_5779_;
v___y_5755_ = v___y_5788_;
v___y_5756_ = v___y_5787_;
v___y_5757_ = v___y_5789_;
v___y_5758_ = v___y_5792_;
v___y_5759_ = v___y_5784_;
v___y_5760_ = v___y_5790_;
v___y_5761_ = v___y_5793_;
v___y_5762_ = v___y_5785_;
v___y_5763_ = v___y_5780_;
v___y_5764_ = v___y_5781_;
v___y_5765_ = v___y_5786_;
v___y_5766_ = v___y_5791_;
v___y_5767_ = v___y_5783_;
goto v___jp_5753_;
}
}
}
else
{
lean_object* v_a_5851_; lean_object* v___x_5853_; uint8_t v_isShared_5854_; uint8_t v_isSharedCheck_5858_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_a_5851_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5853_ = v___x_5831_;
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
else
{
lean_inc(v_a_5851_);
lean_dec(v___x_5831_);
v___x_5853_ = lean_box(0);
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
v_resetjp_5852_:
{
lean_object* v___x_5856_; 
if (v_isShared_5854_ == 0)
{
v___x_5856_ = v___x_5853_;
goto v_reusejp_5855_;
}
else
{
lean_object* v_reuseFailAlloc_5857_; 
v_reuseFailAlloc_5857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5857_, 0, v_a_5851_);
v___x_5856_ = v_reuseFailAlloc_5857_;
goto v_reusejp_5855_;
}
v_reusejp_5855_:
{
return v___x_5856_;
}
}
}
}
}
else
{
lean_object* v_a_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5866_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_a_5859_ = lean_ctor_get(v___x_5828_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5828_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5861_ = v___x_5828_;
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5828_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5864_; 
if (v_isShared_5862_ == 0)
{
v___x_5864_ = v___x_5861_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v_a_5859_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
}
}
}
else
{
lean_object* v_a_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5874_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_a_5867_ = lean_ctor_get(v___x_5807_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5869_ = v___x_5807_;
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5807_);
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
else
{
lean_object* v_a_5875_; lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5882_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_a_5875_ = lean_ctor_get(v___x_5804_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5804_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5877_ = v___x_5804_;
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
else
{
lean_inc(v_a_5875_);
lean_dec(v___x_5804_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v___x_5880_; 
if (v_isShared_5878_ == 0)
{
v___x_5880_ = v___x_5877_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
}
}
}
else
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_a_5883_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5801_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5801_);
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
}
else
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5895_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v___x_5891_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v___y_5780_);
lean_dec_ref(v___y_5780_);
v___x_5892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5891_);
v___x_5893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5892_);
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_5893_);
v___x_5895_ = v___x_5798_;
goto v_reusejp_5894_;
}
else
{
lean_object* v_reuseFailAlloc_5896_; 
v_reuseFailAlloc_5896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5896_, 0, v___x_5893_);
v___x_5895_ = v_reuseFailAlloc_5896_;
goto v_reusejp_5894_;
}
v_reusejp_5894_:
{
return v___x_5895_;
}
}
}
}
else
{
lean_object* v_a_5898_; lean_object* v___x_5900_; uint8_t v_isShared_5901_; uint8_t v_isSharedCheck_5905_; 
lean_dec_ref(v___x_5794_);
lean_dec_ref(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec_ref(v___y_5779_);
lean_dec(v_goal_5687_);
v_a_5898_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_5905_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5905_ == 0)
{
v___x_5900_ = v___x_5795_;
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
else
{
lean_inc(v_a_5898_);
lean_dec(v___x_5795_);
v___x_5900_ = lean_box(0);
v_isShared_5901_ = v_isSharedCheck_5905_;
goto v_resetjp_5899_;
}
v_resetjp_5899_:
{
lean_object* v___x_5903_; 
if (v_isShared_5901_ == 0)
{
v___x_5903_ = v___x_5900_;
goto v_reusejp_5902_;
}
else
{
lean_object* v_reuseFailAlloc_5904_; 
v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
v___x_5903_ = v_reuseFailAlloc_5904_;
goto v_reusejp_5902_;
}
v_reusejp_5902_:
{
return v___x_5903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_6167_, lean_object* v_scope_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_, lean_object* v___y_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_, lean_object* v___y_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_, lean_object* v___y_6179_, lean_object* v___y_6180_){
_start:
{
lean_object* v_res_6181_; 
v_res_6181_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_6167_, v_scope_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
lean_dec(v___y_6179_);
lean_dec_ref(v___y_6178_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
lean_dec(v___y_6175_);
lean_dec_ref(v___y_6174_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v___y_6171_);
lean_dec(v___y_6170_);
lean_dec_ref(v___y_6169_);
return v_res_6181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_scope_6182_, lean_object* v_goal_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_, lean_object* v_a_6193_, lean_object* v_a_6194_){
_start:
{
lean_object* v___f_6196_; lean_object* v___x_6197_; 
lean_inc(v_goal_6183_);
v___f_6196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6196_, 0, v_goal_6183_);
lean_closure_set(v___f_6196_, 1, v_scope_6182_);
v___x_6197_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6183_, v___f_6196_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_, v_a_6193_, v_a_6194_);
return v___x_6197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_scope_6198_, lean_object* v_goal_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v_a_6202_, lean_object* v_a_6203_, lean_object* v_a_6204_, lean_object* v_a_6205_, lean_object* v_a_6206_, lean_object* v_a_6207_, lean_object* v_a_6208_, lean_object* v_a_6209_, lean_object* v_a_6210_, lean_object* v_a_6211_){
_start:
{
lean_object* v_res_6212_; 
v_res_6212_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_6198_, v_goal_6199_, v_a_6200_, v_a_6201_, v_a_6202_, v_a_6203_, v_a_6204_, v_a_6205_, v_a_6206_, v_a_6207_, v_a_6208_, v_a_6209_, v_a_6210_);
lean_dec(v_a_6210_);
lean_dec_ref(v_a_6209_);
lean_dec(v_a_6208_);
lean_dec_ref(v_a_6207_);
lean_dec(v_a_6206_);
lean_dec_ref(v_a_6205_);
lean_dec(v_a_6204_);
lean_dec_ref(v_a_6203_);
lean_dec(v_a_6202_);
lean_dec(v_a_6201_);
lean_dec_ref(v_a_6200_);
return v_res_6212_;
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
