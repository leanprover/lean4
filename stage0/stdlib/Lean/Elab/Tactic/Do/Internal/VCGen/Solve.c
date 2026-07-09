// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Solve
// Imports: public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache public import Lean.Elab.Tactic.Do.Internal.VCGen.Entails public import Lean.Meta.Sym.InstantiateS import Lean.Meta.Sym.InferType
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_isJP(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_fvarId_x3f(lean_object*);
lean_object* l_Lean_FVarId_getValue_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(lean_object*);
lean_object* l_Lean_Meta_Sym_getMatch___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 127, 121, 224, 88, 246, 48, 72)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(114, 80, 184, 106, 225, 60, 114, 167)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Spec for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Applying a spec for "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = ". Excess args: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`until` pattern matched program "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "; stopping"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`frames` matched "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "; frame:"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_framed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_framed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_notFramed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_notFramed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "meet_wp_imp_le_wp_skipFrame"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "frame rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "frame: failed to apply rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "frame: failed to build rule for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "frame: could not build spec from meet_wp_imp_le_wp_skipFrame for"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___boxed(lean_object**);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Gadget"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "skipFrame"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 34, 209, 230, 196, 66, 78, 134)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__1_value),LEAN_SCALAR_PTR_LITERAL(16, 131, 164, 26, 175, 104, 180, 134)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_useJP_329_ = lean_ctor_get_uint8(v_a_320_, sizeof(void*)*4 + 1);
if (v_useJP_329_ == 0)
{
lean_dec(v_name_318_);
goto v___jp_326_;
}
else
{
uint8_t v___x_330_; 
lean_inc(v_name_318_);
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
lean_object* v_declName_510_; lean_object* v_value_511_; lean_object* v_body_512_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___x_550_; 
v_declName_510_ = lean_ctor_get(v_target_466_, 0);
lean_inc_n(v_declName_510_, 2);
v_value_511_ = lean_ctor_get(v_target_466_, 2);
lean_inc_ref(v_value_511_);
v_body_512_ = lean_ctor_get(v_target_466_, 3);
lean_inc_ref(v_body_512_);
lean_dec_ref_known(v_target_466_, 4);
v___x_550_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_510_, v_value_511_, v_a_467_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_550_) == 0)
{
uint8_t v___x_551_; 
lean_dec_ref_known(v___x_550_, 1);
v___x_551_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_511_);
if (v___x_551_ == 0)
{
lean_object* v_options_552_; uint8_t v_hasTrace_553_; 
lean_dec_ref(v_body_512_);
lean_dec_ref(v_value_511_);
v_options_552_ = lean_ctor_get(v_a_476_, 2);
v_hasTrace_553_ = lean_ctor_get_uint8(v_options_552_, sizeof(void*)*1);
if (v_hasTrace_553_ == 0)
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
lean_object* v_inheritedTraceOptions_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_inheritedTraceOptions_554_ = lean_ctor_get(v_a_476_, 13);
v___x_555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_556_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_554_, v_options_552_, v___x_556_);
if (v___x_557_ == 0)
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
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_558_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9);
v___x_559_ = l_Lean_MessageData_ofName(v_declName_510_);
v___x_560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_558_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_555_, v___x_560_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_dec_ref_known(v___x_561_, 1);
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
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_goal_465_);
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
}
}
else
{
lean_object* v_options_570_; uint8_t v_hasTrace_571_; 
v_options_570_ = lean_ctor_get(v_a_476_, 2);
v_hasTrace_571_ = lean_ctor_get_uint8(v_options_570_, sizeof(void*)*1);
if (v_hasTrace_571_ == 0)
{
lean_dec(v_declName_510_);
v___y_514_ = v_a_473_;
v___y_515_ = v_a_474_;
v___y_516_ = v_a_475_;
v___y_517_ = v_a_476_;
v___y_518_ = v_a_477_;
goto v___jp_513_;
}
else
{
lean_object* v_inheritedTraceOptions_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_inheritedTraceOptions_572_ = lean_ctor_get(v_a_476_, 13);
v___x_573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_574_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_575_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_572_, v_options_570_, v___x_574_);
if (v___x_575_ == 0)
{
lean_dec(v_declName_510_);
v___y_514_ = v_a_473_;
v___y_515_ = v_a_474_;
v___y_516_ = v_a_475_;
v___y_517_ = v_a_476_;
v___y_518_ = v_a_477_;
goto v___jp_513_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_576_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_577_ = l_Lean_MessageData_ofName(v_declName_510_);
v___x_578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_576_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v___x_579_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_573_, v___x_578_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_dec_ref_known(v___x_579_, 1);
v___y_514_ = v_a_473_;
v___y_515_ = v_a_474_;
v___y_516_ = v_a_475_;
v___y_517_ = v_a_476_;
v___y_518_ = v_a_477_;
goto v___jp_513_;
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v_body_512_);
lean_dec_ref(v_value_511_);
lean_dec(v_goal_465_);
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_dec_ref(v_body_512_);
lean_dec_ref(v_value_511_);
lean_dec(v_declName_510_);
lean_dec(v_goal_465_);
v_a_588_ = lean_ctor_get(v___x_550_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_550_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_550_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_550_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
v___jp_513_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = lean_unsigned_to_nat(1u);
v___x_520_ = lean_mk_empty_array_with_capacity(v___x_519_);
v___x_521_ = lean_array_push(v___x_520_, v_value_511_);
v___x_522_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_body_512_, v___x_521_, v___y_514_);
lean_dec_ref(v___x_521_);
if (lean_obj_tag(v___x_522_) == 0)
{
lean_object* v_a_523_; lean_object* v___x_524_; 
v_a_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___x_522_, 1);
v___x_524_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_465_, v_a_523_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_533_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_533_ == 0)
{
v___x_527_ = v___x_524_;
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_524_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_533_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v_a_525_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_529_);
v___x_531_ = v___x_527_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_524_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_524_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_524_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_524_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
lean_dec(v_goal_465_);
v_a_542_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_522_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_522_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec_ref(v_target_466_);
lean_dec(v_goal_465_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___boxed(lean_object* v_goal_598_, lean_object* v_target_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_598_, v_target_599_, v_a_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_, v_a_610_);
lean_dec(v_a_610_);
lean_dec_ref(v_a_609_);
lean_dec(v_a_608_);
lean_dec_ref(v_a_607_);
lean_dec(v_a_606_);
lean_dec_ref(v_a_605_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec(v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(lean_object* v_cls_613_, lean_object* v_msg_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_613_, v_msg_614_, v___y_622_, v___y_623_, v___y_624_, v___y_625_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object* v_cls_628_, lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(v_cls_628_, v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
lean_dec(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(lean_object* v_goal_651_, lean_object* v_target_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3));
v___x_666_ = l_Lean_Expr_isAppOf(v_target_652_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_goal_651_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(v_goal_651_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_, v_a_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v___x_669_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_669_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_a_670_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_674_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
else
{
lean_object* v_a_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_686_; 
v_a_679_ = lean_ctor_get(v___x_669_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_669_);
if (v_isSharedCheck_686_ == 0)
{
v___x_681_ = v___x_669_;
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_a_679_);
lean_dec(v___x_669_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_686_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_684_; 
if (v_isShared_682_ == 0)
{
v___x_684_ = v___x_681_;
goto v_reusejp_683_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
v___x_684_ = v_reuseFailAlloc_685_;
goto v_reusejp_683_;
}
v_reusejp_683_:
{
return v___x_684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_687_, lean_object* v_target_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_687_, v_target_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_);
lean_dec(v_a_699_);
lean_dec_ref(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec(v_a_690_);
lean_dec_ref(v_a_689_);
lean_dec_ref(v_target_688_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_x_712_){
_start:
{
uint8_t v___y_714_; 
if (lean_obj_tag(v_x_710_) == 5)
{
lean_object* v_fn_723_; lean_object* v_arg_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v_fn_723_ = lean_ctor_get(v_x_710_, 0);
lean_inc_ref(v_fn_723_);
v_arg_724_ = lean_ctor_get(v_x_710_, 1);
lean_inc_ref(v_arg_724_);
lean_dec_ref_known(v_x_710_, 2);
v___x_725_ = lean_array_set(v_x_711_, v_x_712_, v_arg_724_);
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = lean_nat_sub(v_x_712_, v___x_726_);
lean_dec(v_x_712_);
v_x_710_ = v_fn_723_;
v_x_711_ = v___x_725_;
v_x_712_ = v___x_727_;
goto _start;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
lean_dec(v_x_712_);
v___x_729_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2));
v___x_730_ = l_Lean_Expr_isConstOf(v_x_710_, v___x_729_);
if (v___x_730_ == 0)
{
v___y_714_ = v___x_730_;
goto v___jp_713_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_unsigned_to_nat(10u);
v___x_732_ = lean_array_get_size(v_x_711_);
v___x_733_ = lean_nat_dec_le(v___x_731_, v___x_732_);
v___y_714_ = v___x_733_;
goto v___jp_713_;
}
}
v___jp_713_:
{
if (v___y_714_ == 0)
{
lean_object* v___x_715_; 
lean_dec_ref(v_x_711_);
lean_dec_ref(v_x_710_);
v___x_715_ = lean_box(0);
return v___x_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
v___x_716_ = lean_unsigned_to_nat(10u);
v___x_717_ = lean_unsigned_to_nat(0u);
v___x_718_ = l_Array_extract___redArg(v_x_711_, v___x_717_, v___x_716_);
v___x_719_ = lean_array_get_size(v_x_711_);
v___x_720_ = l_Array_extract___redArg(v_x_711_, v___x_716_, v___x_719_);
lean_dec_ref(v_x_711_);
v___x_721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_721_, 0, v_x_710_);
lean_ctor_set(v___x_721_, 1, v___x_718_);
lean_ctor_set(v___x_721_, 2, v___x_720_);
v___x_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v_dummy_735_; 
v___x_734_ = lean_box(0);
v_dummy_735_ = l_Lean_Expr_sort___override(v___x_734_);
return v_dummy_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(lean_object* v_rhs_736_){
_start:
{
lean_object* v_dummy_737_; lean_object* v_nargs_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_dummy_737_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_738_ = l_Lean_Expr_getAppNumArgs(v_rhs_736_);
lean_inc(v_nargs_738_);
v___x_739_ = lean_mk_array(v_nargs_738_, v_dummy_737_);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_sub(v_nargs_738_, v___x_740_);
lean_dec(v_nargs_738_);
v___x_742_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(v_rhs_736_, v___x_739_, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_x_745_, lean_object* v_x_746_){
_start:
{
lean_object* v_ks_747_; lean_object* v_vs_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_772_; 
v_ks_747_ = lean_ctor_get(v_x_743_, 0);
v_vs_748_ = lean_ctor_get(v_x_743_, 1);
v_isSharedCheck_772_ = !lean_is_exclusive(v_x_743_);
if (v_isSharedCheck_772_ == 0)
{
v___x_750_ = v_x_743_;
v_isShared_751_ = v_isSharedCheck_772_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_vs_748_);
lean_inc(v_ks_747_);
lean_dec(v_x_743_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_772_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_752_ = lean_array_get_size(v_ks_747_);
v___x_753_ = lean_nat_dec_lt(v_x_744_, v___x_752_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
lean_dec(v_x_744_);
v___x_754_ = lean_array_push(v_ks_747_, v_x_745_);
v___x_755_ = lean_array_push(v_vs_748_, v_x_746_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_755_);
lean_ctor_set(v___x_750_, 0, v___x_754_);
v___x_757_ = v___x_750_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
else
{
lean_object* v_k_x27_759_; uint8_t v___x_760_; 
v_k_x27_759_ = lean_array_fget_borrowed(v_ks_747_, v_x_744_);
v___x_760_ = l_Lean_instBEqMVarId_beq(v_x_745_, v_k_x27_759_);
if (v___x_760_ == 0)
{
lean_object* v___x_762_; 
if (v_isShared_751_ == 0)
{
v___x_762_ = v___x_750_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_ks_747_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_vs_748_);
v___x_762_ = v_reuseFailAlloc_766_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_add(v_x_744_, v___x_763_);
lean_dec(v_x_744_);
v_x_743_ = v___x_762_;
v_x_744_ = v___x_764_;
goto _start;
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_770_; 
v___x_767_ = lean_array_fset(v_ks_747_, v_x_744_, v_x_745_);
v___x_768_ = lean_array_fset(v_vs_748_, v_x_744_, v_x_746_);
lean_dec(v_x_744_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 1, v___x_768_);
lean_ctor_set(v___x_750_, 0, v___x_767_);
v___x_770_ = v___x_750_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_767_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_773_, lean_object* v_k_774_, lean_object* v_v_775_){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_773_, v___x_776_, v_k_774_, v_v_775_);
return v___x_777_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_779_, size_t v_x_780_, size_t v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
if (lean_obj_tag(v_x_779_) == 0)
{
lean_object* v_es_784_; size_t v___x_785_; size_t v___x_786_; lean_object* v_j_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_es_784_ = lean_ctor_get(v_x_779_, 0);
v___x_785_ = ((size_t)31ULL);
v___x_786_ = lean_usize_land(v_x_780_, v___x_785_);
v_j_787_ = lean_usize_to_nat(v___x_786_);
v___x_788_ = lean_array_get_size(v_es_784_);
v___x_789_ = lean_nat_dec_lt(v_j_787_, v___x_788_);
if (v___x_789_ == 0)
{
lean_dec(v_j_787_);
lean_dec(v_x_783_);
lean_dec(v_x_782_);
return v_x_779_;
}
else
{
lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_828_; 
lean_inc_ref(v_es_784_);
v_isSharedCheck_828_ = !lean_is_exclusive(v_x_779_);
if (v_isSharedCheck_828_ == 0)
{
lean_object* v_unused_829_; 
v_unused_829_ = lean_ctor_get(v_x_779_, 0);
lean_dec(v_unused_829_);
v___x_791_ = v_x_779_;
v_isShared_792_ = v_isSharedCheck_828_;
goto v_resetjp_790_;
}
else
{
lean_dec(v_x_779_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_828_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v_v_793_; lean_object* v___x_794_; lean_object* v_xs_x27_795_; lean_object* v___y_797_; 
v_v_793_ = lean_array_fget(v_es_784_, v_j_787_);
v___x_794_ = lean_box(0);
v_xs_x27_795_ = lean_array_fset(v_es_784_, v_j_787_, v___x_794_);
switch(lean_obj_tag(v_v_793_))
{
case 0:
{
lean_object* v_key_802_; lean_object* v_val_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_813_; 
v_key_802_ = lean_ctor_get(v_v_793_, 0);
v_val_803_ = lean_ctor_get(v_v_793_, 1);
v_isSharedCheck_813_ = !lean_is_exclusive(v_v_793_);
if (v_isSharedCheck_813_ == 0)
{
v___x_805_ = v_v_793_;
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_val_803_);
lean_inc(v_key_802_);
lean_dec(v_v_793_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_813_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = l_Lean_instBEqMVarId_beq(v_x_782_, v_key_802_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_del_object(v___x_805_);
v___x_808_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_802_, v_val_803_, v_x_782_, v_x_783_);
v___x_809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
v___y_797_ = v___x_809_;
goto v___jp_796_;
}
else
{
lean_object* v___x_811_; 
lean_dec(v_val_803_);
lean_dec(v_key_802_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_x_783_);
lean_ctor_set(v___x_805_, 0, v_x_782_);
v___x_811_ = v___x_805_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_x_782_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v_x_783_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_797_ = v___x_811_;
goto v___jp_796_;
}
}
}
}
case 1:
{
lean_object* v_node_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_826_; 
v_node_814_ = lean_ctor_get(v_v_793_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v_v_793_);
if (v_isSharedCheck_826_ == 0)
{
v___x_816_ = v_v_793_;
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_node_814_);
lean_dec(v_v_793_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_826_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
size_t v___x_818_; size_t v___x_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_818_ = ((size_t)5ULL);
v___x_819_ = lean_usize_shift_right(v_x_780_, v___x_818_);
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_x_781_, v___x_820_);
v___x_822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_814_, v___x_819_, v___x_821_, v_x_782_, v_x_783_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 0, v___x_822_);
v___x_824_ = v___x_816_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v___y_797_ = v___x_824_;
goto v___jp_796_;
}
}
}
default: 
{
lean_object* v___x_827_; 
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v_x_782_);
lean_ctor_set(v___x_827_, 1, v_x_783_);
v___y_797_ = v___x_827_;
goto v___jp_796_;
}
}
v___jp_796_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_array_fset(v_xs_x27_795_, v_j_787_, v___y_797_);
lean_dec(v_j_787_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_798_);
v___x_800_ = v___x_791_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
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
}
else
{
lean_object* v_ks_830_; lean_object* v_vs_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_851_; 
v_ks_830_ = lean_ctor_get(v_x_779_, 0);
v_vs_831_ = lean_ctor_get(v_x_779_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_x_779_);
if (v_isSharedCheck_851_ == 0)
{
v___x_833_ = v_x_779_;
v_isShared_834_ = v_isSharedCheck_851_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_vs_831_);
lean_inc(v_ks_830_);
lean_dec(v_x_779_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_851_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_ks_830_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v_vs_831_);
v___x_836_ = v_reuseFailAlloc_850_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
lean_object* v_newNode_837_; uint8_t v___y_839_; size_t v___x_845_; uint8_t v___x_846_; 
v_newNode_837_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_836_, v_x_782_, v_x_783_);
v___x_845_ = ((size_t)7ULL);
v___x_846_ = lean_usize_dec_le(v___x_845_, v_x_781_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_847_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_837_);
v___x_848_ = lean_unsigned_to_nat(4u);
v___x_849_ = lean_nat_dec_lt(v___x_847_, v___x_848_);
lean_dec(v___x_847_);
v___y_839_ = v___x_849_;
goto v___jp_838_;
}
else
{
v___y_839_ = v___x_846_;
goto v___jp_838_;
}
v___jp_838_:
{
if (v___y_839_ == 0)
{
lean_object* v_ks_840_; lean_object* v_vs_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_ks_840_ = lean_ctor_get(v_newNode_837_, 0);
lean_inc_ref(v_ks_840_);
v_vs_841_ = lean_ctor_get(v_newNode_837_, 1);
lean_inc_ref(v_vs_841_);
lean_dec_ref(v_newNode_837_);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_781_, v_ks_840_, v_vs_841_, v___x_842_, v___x_843_);
lean_dec_ref(v_vs_841_);
lean_dec_ref(v_ks_840_);
return v___x_844_;
}
else
{
return v_newNode_837_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_852_, lean_object* v_keys_853_, lean_object* v_vals_854_, lean_object* v_i_855_, lean_object* v_entries_856_){
_start:
{
lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_857_ = lean_array_get_size(v_keys_853_);
v___x_858_ = lean_nat_dec_lt(v_i_855_, v___x_857_);
if (v___x_858_ == 0)
{
lean_dec(v_i_855_);
return v_entries_856_;
}
else
{
lean_object* v_k_859_; lean_object* v_v_860_; uint64_t v___x_861_; size_t v_h_862_; size_t v___x_863_; lean_object* v___x_864_; size_t v___x_865_; size_t v___x_866_; size_t v___x_867_; size_t v_h_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_k_859_ = lean_array_fget_borrowed(v_keys_853_, v_i_855_);
v_v_860_ = lean_array_fget_borrowed(v_vals_854_, v_i_855_);
v___x_861_ = l_Lean_instHashableMVarId_hash(v_k_859_);
v_h_862_ = lean_uint64_to_usize(v___x_861_);
v___x_863_ = ((size_t)5ULL);
v___x_864_ = lean_unsigned_to_nat(1u);
v___x_865_ = ((size_t)1ULL);
v___x_866_ = lean_usize_sub(v_depth_852_, v___x_865_);
v___x_867_ = lean_usize_mul(v___x_863_, v___x_866_);
v_h_868_ = lean_usize_shift_right(v_h_862_, v___x_867_);
v___x_869_ = lean_nat_add(v_i_855_, v___x_864_);
lean_dec(v_i_855_);
lean_inc(v_v_860_);
lean_inc(v_k_859_);
v___x_870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_856_, v_h_868_, v_depth_852_, v_k_859_, v_v_860_);
v_i_855_ = v___x_869_;
v_entries_856_ = v___x_870_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_872_, lean_object* v_keys_873_, lean_object* v_vals_874_, lean_object* v_i_875_, lean_object* v_entries_876_){
_start:
{
size_t v_depth_boxed_877_; lean_object* v_res_878_; 
v_depth_boxed_877_ = lean_unbox_usize(v_depth_872_);
lean_dec(v_depth_872_);
v_res_878_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_877_, v_keys_873_, v_vals_874_, v_i_875_, v_entries_876_);
lean_dec_ref(v_vals_874_);
lean_dec_ref(v_keys_873_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_){
_start:
{
size_t v_x_8514__boxed_884_; size_t v_x_8515__boxed_885_; lean_object* v_res_886_; 
v_x_8514__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_x_8515__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_res_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_879_, v_x_8514__boxed_884_, v_x_8515__boxed_885_, v_x_882_, v_x_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
uint64_t v___x_890_; size_t v___x_891_; size_t v___x_892_; lean_object* v___x_893_; 
v___x_890_ = l_Lean_instHashableMVarId_hash(v_x_888_);
v___x_891_ = lean_uint64_to_usize(v___x_890_);
v___x_892_ = ((size_t)1ULL);
v___x_893_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_887_, v___x_891_, v___x_892_, v_x_888_, v_x_889_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_894_, lean_object* v_val_895_, lean_object* v___y_896_){
_start:
{
lean_object* v___x_898_; lean_object* v_mctx_899_; lean_object* v_cache_900_; lean_object* v_zetaDeltaFVarIds_901_; lean_object* v_postponed_902_; lean_object* v_diag_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_931_; 
v___x_898_ = lean_st_ref_take(v___y_896_);
v_mctx_899_ = lean_ctor_get(v___x_898_, 0);
v_cache_900_ = lean_ctor_get(v___x_898_, 1);
v_zetaDeltaFVarIds_901_ = lean_ctor_get(v___x_898_, 2);
v_postponed_902_ = lean_ctor_get(v___x_898_, 3);
v_diag_903_ = lean_ctor_get(v___x_898_, 4);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_931_ == 0)
{
v___x_905_ = v___x_898_;
v_isShared_906_ = v_isSharedCheck_931_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_diag_903_);
lean_inc(v_postponed_902_);
lean_inc(v_zetaDeltaFVarIds_901_);
lean_inc(v_cache_900_);
lean_inc(v_mctx_899_);
lean_dec(v___x_898_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_931_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v_depth_907_; lean_object* v_levelAssignDepth_908_; lean_object* v_lmvarCounter_909_; lean_object* v_mvarCounter_910_; lean_object* v_lDecls_911_; lean_object* v_decls_912_; lean_object* v_userNames_913_; lean_object* v_lAssignment_914_; lean_object* v_eAssignment_915_; lean_object* v_dAssignment_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_930_; 
v_depth_907_ = lean_ctor_get(v_mctx_899_, 0);
v_levelAssignDepth_908_ = lean_ctor_get(v_mctx_899_, 1);
v_lmvarCounter_909_ = lean_ctor_get(v_mctx_899_, 2);
v_mvarCounter_910_ = lean_ctor_get(v_mctx_899_, 3);
v_lDecls_911_ = lean_ctor_get(v_mctx_899_, 4);
v_decls_912_ = lean_ctor_get(v_mctx_899_, 5);
v_userNames_913_ = lean_ctor_get(v_mctx_899_, 6);
v_lAssignment_914_ = lean_ctor_get(v_mctx_899_, 7);
v_eAssignment_915_ = lean_ctor_get(v_mctx_899_, 8);
v_dAssignment_916_ = lean_ctor_get(v_mctx_899_, 9);
v_isSharedCheck_930_ = !lean_is_exclusive(v_mctx_899_);
if (v_isSharedCheck_930_ == 0)
{
v___x_918_ = v_mctx_899_;
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_dAssignment_916_);
lean_inc(v_eAssignment_915_);
lean_inc(v_lAssignment_914_);
lean_inc(v_userNames_913_);
lean_inc(v_decls_912_);
lean_inc(v_lDecls_911_);
lean_inc(v_mvarCounter_910_);
lean_inc(v_lmvarCounter_909_);
lean_inc(v_levelAssignDepth_908_);
lean_inc(v_depth_907_);
lean_dec(v_mctx_899_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_930_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_915_, v_mvarId_894_, v_val_895_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 8, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_depth_907_);
lean_ctor_set(v_reuseFailAlloc_929_, 1, v_levelAssignDepth_908_);
lean_ctor_set(v_reuseFailAlloc_929_, 2, v_lmvarCounter_909_);
lean_ctor_set(v_reuseFailAlloc_929_, 3, v_mvarCounter_910_);
lean_ctor_set(v_reuseFailAlloc_929_, 4, v_lDecls_911_);
lean_ctor_set(v_reuseFailAlloc_929_, 5, v_decls_912_);
lean_ctor_set(v_reuseFailAlloc_929_, 6, v_userNames_913_);
lean_ctor_set(v_reuseFailAlloc_929_, 7, v_lAssignment_914_);
lean_ctor_set(v_reuseFailAlloc_929_, 8, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_929_, 9, v_dAssignment_916_);
v___x_922_ = v_reuseFailAlloc_929_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
lean_object* v___x_924_; 
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_922_);
v___x_924_ = v___x_905_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_cache_900_);
lean_ctor_set(v_reuseFailAlloc_928_, 2, v_zetaDeltaFVarIds_901_);
lean_ctor_set(v_reuseFailAlloc_928_, 3, v_postponed_902_);
lean_ctor_set(v_reuseFailAlloc_928_, 4, v_diag_903_);
v___x_924_ = v_reuseFailAlloc_928_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_st_ref_set(v___y_896_, v___x_924_);
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_932_, lean_object* v_val_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_932_, v_val_933_, v___y_934_);
lean_dec(v___y_934_);
return v_res_936_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = l_Lean_Level_ofNat(v___x_944_);
return v___x_945_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4);
v___x_947_ = l_Lean_mkSort(v___x_946_);
return v___x_947_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5);
v___x_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_949_, 0, v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6);
v___x_952_ = lean_unsigned_to_nat(2u);
v___x_953_ = lean_mk_empty_array_with_capacity(v___x_952_);
v___x_954_ = lean_array_push(v___x_953_, v___x_951_);
v___x_955_ = lean_array_push(v___x_954_, v___x_950_);
return v___x_955_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_968_ = lean_box(0);
v___x_969_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12));
v___x_970_ = l_Lean_mkConst(v___x_969_, v___x_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(lean_object* v_goal_971_, lean_object* v_target_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
lean_inc_ref(v_target_972_);
v___x_985_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(v_target_972_);
if (lean_obj_tag(v___x_985_) == 1)
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1052_; 
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_1053_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_1052_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1052_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_989_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_990_ = lean_unsigned_to_nat(2u);
v___x_991_ = lean_mk_empty_array_with_capacity(v___x_990_);
v___x_992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7);
v___x_993_ = l_Lean_Meta_mkAppOptM(v___x_989_, v___x_992_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_a_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec_ref_known(v___x_993_, 1);
v___x_995_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_996_ = lean_array_push(v___x_991_, v_a_994_);
lean_inc_ref(v_target_972_);
v___x_997_ = lean_array_push(v___x_996_, v_target_972_);
v___x_998_ = l_Lean_Meta_mkAppM(v___x_995_, v___x_997_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_999_, v_a_979_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec_ref_known(v___x_1000_, 1);
v___x_1002_ = lean_box(0);
v___x_1003_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1001_, v___x_1002_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1018_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc_n(v_a_1004_, 2);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13);
v___x_1006_ = l_Lean_mkAppB(v___x_1005_, v_target_972_, v_a_1004_);
v___x_1007_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_971_, v___x_1006_, v_a_981_);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1019_);
v___x_1009_ = v___x_1007_;
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_1007_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1018_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1013_; 
v___x_1011_ = l_Lean_Expr_mvarId_x21(v_a_1004_);
lean_dec(v_a_1004_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_1011_);
v___x_1013_ = v___x_987_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1011_);
v___x_1013_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
lean_object* v___x_1015_; 
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1013_);
v___x_1015_ = v___x_1009_;
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
}
else
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
lean_del_object(v___x_987_);
lean_dec_ref(v_target_972_);
lean_dec(v_goal_971_);
v_a_1020_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1022_ = v___x_1003_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1003_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_del_object(v___x_987_);
lean_dec_ref(v_target_972_);
lean_dec(v_goal_971_);
v_a_1028_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1000_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1000_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_del_object(v___x_987_);
lean_dec_ref(v_target_972_);
lean_dec(v_goal_971_);
v_a_1036_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_998_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_998_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
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
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___x_991_);
lean_del_object(v___x_987_);
lean_dec_ref(v_target_972_);
lean_dec(v_goal_971_);
v_a_1044_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_993_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_993_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec(v___x_985_);
lean_dec_ref(v_target_972_);
lean_dec(v_goal_971_);
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1056_, lean_object* v_target_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_1056_, v_target_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec_ref(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1071_, lean_object* v_val_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1071_, v_val_1072_, v___y_1081_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1086_, lean_object* v_val_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1086_, v_val_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
lean_dec_ref(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1101_, lean_object* v_x_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1102_, v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1106_, lean_object* v_x_1107_, size_t v_x_1108_, size_t v_x_1109_, lean_object* v_x_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1107_, v_x_1108_, v_x_1109_, v_x_1110_, v_x_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_){
_start:
{
size_t v_x_9024__boxed_1119_; size_t v_x_9025__boxed_1120_; lean_object* v_res_1121_; 
v_x_9024__boxed_1119_ = lean_unbox_usize(v_x_1115_);
lean_dec(v_x_1115_);
v_x_9025__boxed_1120_ = lean_unbox_usize(v_x_1116_);
lean_dec(v_x_1116_);
v_res_1121_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1113_, v_x_1114_, v_x_9024__boxed_1119_, v_x_9025__boxed_1120_, v_x_1117_, v_x_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1122_, lean_object* v_n_1123_, lean_object* v_k_1124_, lean_object* v_v_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1123_, v_k_1124_, v_v_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1127_, size_t v_depth_1128_, lean_object* v_keys_1129_, lean_object* v_vals_1130_, lean_object* v_heq_1131_, lean_object* v_i_1132_, lean_object* v_entries_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1128_, v_keys_1129_, v_vals_1130_, v_i_1132_, v_entries_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1135_, lean_object* v_depth_1136_, lean_object* v_keys_1137_, lean_object* v_vals_1138_, lean_object* v_heq_1139_, lean_object* v_i_1140_, lean_object* v_entries_1141_){
_start:
{
size_t v_depth_boxed_1142_; lean_object* v_res_1143_; 
v_depth_boxed_1142_ = lean_unbox_usize(v_depth_1136_);
lean_dec(v_depth_1136_);
v_res_1143_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1135_, v_depth_boxed_1142_, v_keys_1137_, v_vals_1138_, v_heq_1139_, v_i_1140_, v_entries_1141_);
lean_dec_ref(v_vals_1138_);
lean_dec_ref(v_keys_1137_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1145_, v_x_1146_, v_x_1147_, v_x_1148_);
return v___x_1149_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0));
v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(lean_object* v_goal_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_){
_start:
{
lean_object* v_backwardRules_1162_; lean_object* v_refl_1163_; lean_object* v___x_1164_; 
v_backwardRules_1162_ = lean_ctor_get(v_a_1154_, 0);
v_refl_1163_ = lean_ctor_get(v_backwardRules_1162_, 7);
lean_inc_ref(v_refl_1163_);
lean_inc(v_goal_1153_);
v___x_1164_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1153_, v_refl_1163_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1203_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1203_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1203_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
if (lean_obj_tag(v_a_1165_) == 1)
{
lean_object* v_mvarIds_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1198_; 
v_mvarIds_1169_ = lean_ctor_get(v_a_1165_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_a_1165_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1171_ = v_a_1165_;
v_isShared_1172_ = v_isSharedCheck_1198_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_mvarIds_1169_);
lean_dec(v_a_1165_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1198_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_options_1180_; uint8_t v_hasTrace_1181_; 
v_options_1180_ = lean_ctor_get(v_a_1159_, 2);
v_hasTrace_1181_ = lean_ctor_get_uint8(v_options_1180_, sizeof(void*)*1);
if (v_hasTrace_1181_ == 0)
{
lean_dec(v_goal_1153_);
goto v___jp_1173_;
}
else
{
lean_object* v_inheritedTraceOptions_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_inheritedTraceOptions_1182_ = lean_ctor_get(v_a_1159_, 13);
v___x_1183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1184_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1182_, v_options_1180_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_dec(v_goal_1153_);
goto v___jp_1173_;
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1186_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1);
v___x_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1187_, 0, v_goal_1153_);
v___x_1188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1188_, 0, v___x_1186_);
lean_ctor_set(v___x_1188_, 1, v___x_1187_);
v___x_1189_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1183_, v___x_1188_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_dec_ref_known(v___x_1189_, 1);
goto v___jp_1173_;
}
else
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1197_; 
lean_del_object(v___x_1171_);
lean_dec(v_mvarIds_1169_);
lean_del_object(v___x_1167_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1197_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_a_1190_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
}
v___jp_1173_:
{
lean_object* v___x_1175_; 
if (v_isShared_1172_ == 0)
{
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_mvarIds_1169_);
v___x_1175_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1175_);
v___x_1177_ = v___x_1167_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
lean_dec(v_a_1165_);
lean_dec(v_goal_1153_);
v___x_1199_ = lean_box(0);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1199_);
v___x_1201_ = v___x_1167_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_goal_1153_);
v_a_1204_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1164_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1164_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1212_, v_a_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_a_1214_);
lean_dec_ref(v_a_1213_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(lean_object* v_goal_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_, lean_object* v_a_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v___x_1235_; 
v___x_1235_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1222_, v_a_1223_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___boxed(lean_object* v_goal_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(v_goal_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec_ref(v_a_1242_);
lean_dec(v_a_1241_);
lean_dec_ref(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec(v_a_1238_);
lean_dec_ref(v_a_1237_);
return v_res_1249_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1251_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1252_ = l_Lean_stringToMessageData(v___x_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1253_, lean_object* v_e_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1260_; 
v_lastLiftedPre_x3f_1260_ = lean_ctor_get(v_scope_1253_, 2);
lean_inc(v_lastLiftedPre_x3f_1260_);
lean_dec_ref(v_scope_1253_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1260_) == 1)
{
lean_object* v_val_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1316_; 
v_val_1261_ = lean_ctor_get(v_lastLiftedPre_x3f_1260_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1260_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1263_ = v_lastLiftedPre_x3f_1260_;
v_isShared_1264_ = v_isSharedCheck_1316_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_val_1261_);
lean_dec(v_lastLiftedPre_x3f_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1316_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v_lctx_1265_; lean_object* v___x_1266_; 
v_lctx_1265_ = lean_ctor_get(v_a_1255_, 2);
lean_inc_ref(v_lctx_1265_);
v___x_1266_ = lean_local_ctx_find(v_lctx_1265_, v_val_1261_);
if (lean_obj_tag(v___x_1266_) == 1)
{
lean_object* v_val_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_val_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_val_1267_);
v___x_1268_ = l_Lean_LocalDecl_type(v_val_1267_);
v___x_1269_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_1254_, v___x_1268_);
lean_dec_ref(v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_val_1267_);
lean_del_object(v___x_1263_);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; 
v_unused_1278_ = lean_ctor_get(v___x_1266_, 0);
lean_dec(v_unused_1278_);
v___x_1271_ = v___x_1266_;
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
else
{
lean_dec(v___x_1266_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1277_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = lean_box(0);
if (v_isShared_1272_ == 0)
{
lean_ctor_set_tag(v___x_1271_, 0);
lean_ctor_set(v___x_1271_, 0, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
else
{
lean_object* v_options_1279_; uint8_t v_hasTrace_1280_; 
v_options_1279_ = lean_ctor_get(v_a_1257_, 2);
v_hasTrace_1280_ = lean_ctor_get_uint8(v_options_1279_, sizeof(void*)*1);
if (v_hasTrace_1280_ == 0)
{
lean_object* v___x_1282_; 
lean_dec(v_val_1267_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1266_);
v___x_1282_ = v___x_1263_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1266_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_inheritedTraceOptions_1284_ = lean_ctor_get(v_a_1257_, 13);
v___x_1285_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1286_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1287_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1284_, v_options_1279_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1289_; 
lean_dec(v_val_1267_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1266_);
v___x_1289_ = v___x_1263_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1266_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_del_object(v___x_1263_);
v___x_1291_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1292_ = l_Lean_LocalDecl_userName(v_val_1267_);
lean_dec(v_val_1267_);
v___x_1293_ = l_Lean_MessageData_ofName(v___x_1292_);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1291_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1285_, v___x_1294_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v___x_1295_, 0);
lean_dec(v_unused_1303_);
v___x_1297_ = v___x_1295_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_dec(v___x_1295_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1266_);
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1266_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref_known(v___x_1266_, 1);
v_a_1304_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1295_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1295_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
lean_dec(v___x_1266_);
v___x_1312_ = lean_box(0);
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1312_);
v___x_1314_ = v___x_1263_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
lean_dec(v_lastLiftedPre_x3f_1260_);
v___x_1317_ = lean_box(0);
v___x_1318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
return v___x_1318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1319_, lean_object* v_e_1320_, lean_object* v_a_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1319_, v_e_1320_, v_a_1321_, v_a_1322_, v_a_1323_, v_a_1324_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
lean_dec(v_a_1322_);
lean_dec_ref(v_a_1321_);
lean_dec_ref(v_e_1320_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(lean_object* v_scope_1327_, lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1327_, v_e_1328_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1342_, lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(v_scope_1342_, v_e_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec_ref(v_e_1343_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
lean_inc(v___y_1364_);
lean_inc_ref(v___y_1363_);
lean_inc(v___y_1362_);
lean_inc_ref(v___y_1361_);
lean_inc(v___y_1360_);
lean_inc(v___y_1359_);
lean_inc_ref(v___y_1358_);
v___x_1370_ = lean_apply_12(v_x_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, lean_box(0));
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v___y_1375_);
lean_dec(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1385_, lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___f_1399_; lean_object* v___x_1400_; 
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1389_);
lean_inc(v___y_1388_);
lean_inc_ref(v___y_1387_);
v___f_1399_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1399_, 0, v_x_1386_);
lean_closure_set(v___f_1399_, 1, v___y_1387_);
lean_closure_set(v___f_1399_, 2, v___y_1388_);
lean_closure_set(v___f_1399_, 3, v___y_1389_);
lean_closure_set(v___f_1399_, 4, v___y_1390_);
lean_closure_set(v___f_1399_, 5, v___y_1391_);
lean_closure_set(v___f_1399_, 6, v___y_1392_);
lean_closure_set(v___f_1399_, 7, v___y_1393_);
v___x_1400_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1385_, v___f_1399_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1400_) == 0)
{
return v___x_1400_;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1400_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1400_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1409_, v_x_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1424_, lean_object* v_mvarId_1425_, lean_object* v_x_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1425_, v_x_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1440_, lean_object* v_mvarId_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1440_, v_mvarId_1441_, v_x_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1461_, lean_object* v_scope_1462_, lean_object* v_rhs_1463_, lean_object* v_pre_1464_, lean_object* v_goal_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
if (v___x_1461_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_goal_1465_);
lean_dec_ref(v_pre_1464_);
lean_dec_ref(v_rhs_1463_);
lean_dec_ref(v_scope_1462_);
v___x_1478_ = lean_box(0);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1462_, v_rhs_1463_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1517_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1517_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1517_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
if (lean_obj_tag(v_a_1481_) == 1)
{
lean_object* v_val_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_del_object(v___x_1483_);
v_val_1485_ = lean_ctor_get(v_a_1481_, 0);
lean_inc(v_val_1485_);
lean_dec_ref_known(v_a_1481_, 1);
v___x_1486_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_1487_ = l_Lean_LocalDecl_toExpr(v_val_1485_);
v___x_1488_ = lean_unsigned_to_nat(3u);
v___x_1489_ = lean_mk_empty_array_with_capacity(v___x_1488_);
v___x_1490_ = lean_array_push(v___x_1489_, v_pre_1464_);
v___x_1491_ = lean_array_push(v___x_1490_, v_rhs_1463_);
v___x_1492_ = lean_array_push(v___x_1491_, v___x_1487_);
v___x_1493_ = l_Lean_Meta_mkAppM(v___x_1486_, v___x_1492_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1503_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1465_, v_a_1494_, v___y_1474_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v___x_1495_, 0);
lean_dec(v_unused_1504_);
v___x_1497_ = v___x_1495_;
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
else
{
lean_dec(v___x_1495_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1503_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1501_; 
v___x_1499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v_goal_1465_);
v_a_1505_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1493_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1493_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
else
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
lean_dec(v_a_1481_);
lean_dec(v_goal_1465_);
lean_dec_ref(v_pre_1464_);
lean_dec_ref(v_rhs_1463_);
v___x_1513_ = lean_box(0);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1513_);
v___x_1515_ = v___x_1483_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec(v_goal_1465_);
lean_dec_ref(v_pre_1464_);
lean_dec_ref(v_rhs_1463_);
v_a_1518_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1480_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1480_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_1526_ = _args[0];
lean_object* v_scope_1527_ = _args[1];
lean_object* v_rhs_1528_ = _args[2];
lean_object* v_pre_1529_ = _args[3];
lean_object* v_goal_1530_ = _args[4];
lean_object* v___y_1531_ = _args[5];
lean_object* v___y_1532_ = _args[6];
lean_object* v___y_1533_ = _args[7];
lean_object* v___y_1534_ = _args[8];
lean_object* v___y_1535_ = _args[9];
lean_object* v___y_1536_ = _args[10];
lean_object* v___y_1537_ = _args[11];
lean_object* v___y_1538_ = _args[12];
lean_object* v___y_1539_ = _args[13];
lean_object* v___y_1540_ = _args[14];
lean_object* v___y_1541_ = _args[15];
lean_object* v___y_1542_ = _args[16];
_start:
{
uint8_t v___x_7757__boxed_1543_; lean_object* v_res_1544_; 
v___x_7757__boxed_1543_ = lean_unbox(v___x_1526_);
v_res_1544_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1543_, v_scope_1527_, v_rhs_1528_, v_pre_1529_, v_goal_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec_ref(v___y_1536_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
lean_dec(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(lean_object* v_scope_1545_, lean_object* v_goal_1546_, lean_object* v_00_u03b1_1547_, lean_object* v_pre_1548_, lean_object* v_rhs_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_){
_start:
{
uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___y_1564_; lean_object* v___x_1565_; 
v___x_1562_ = l_Lean_Expr_isProp(v_00_u03b1_1547_);
v___x_1563_ = lean_box(v___x_1562_);
lean_inc(v_goal_1546_);
v___y_1564_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1564_, 0, v___x_1563_);
lean_closure_set(v___y_1564_, 1, v_scope_1545_);
lean_closure_set(v___y_1564_, 2, v_rhs_1549_);
lean_closure_set(v___y_1564_, 3, v_pre_1548_);
lean_closure_set(v___y_1564_, 4, v_goal_1546_);
v___x_1565_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1546_, v___y_1564_, v_a_1550_, v_a_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_1566_ = _args[0];
lean_object* v_goal_1567_ = _args[1];
lean_object* v_00_u03b1_1568_ = _args[2];
lean_object* v_pre_1569_ = _args[3];
lean_object* v_rhs_1570_ = _args[4];
lean_object* v_a_1571_ = _args[5];
lean_object* v_a_1572_ = _args[6];
lean_object* v_a_1573_ = _args[7];
lean_object* v_a_1574_ = _args[8];
lean_object* v_a_1575_ = _args[9];
lean_object* v_a_1576_ = _args[10];
lean_object* v_a_1577_ = _args[11];
lean_object* v_a_1578_ = _args[12];
lean_object* v_a_1579_ = _args[13];
lean_object* v_a_1580_ = _args[14];
lean_object* v_a_1581_ = _args[15];
lean_object* v_a_1582_ = _args[16];
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_scope_1566_, v_goal_1567_, v_00_u03b1_1568_, v_pre_1569_, v_rhs_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
lean_dec(v_a_1573_);
lean_dec(v_a_1572_);
lean_dec_ref(v_a_1571_);
lean_dec_ref(v_00_u03b1_1568_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1584_, lean_object* v_target_1585_, lean_object* v_goal_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1584_, v_target_1585_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1620_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1602_ = v___x_1599_;
v_isShared_1603_ = v_isSharedCheck_1620_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v___x_1599_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1620_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
if (lean_obj_tag(v_a_1600_) == 1)
{
lean_object* v_val_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1614_; 
lean_del_object(v___x_1602_);
v_val_1604_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_a_1600_, 1);
v___x_1605_ = l_Lean_LocalDecl_toExpr(v_val_1604_);
v___x_1606_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1586_, v___x_1605_, v___y_1595_);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1606_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1606_, 0);
lean_dec(v_unused_1615_);
v___x_1608_ = v___x_1606_;
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v___x_1606_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1614_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1610_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1610_);
v___x_1612_ = v___x_1608_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_dec(v_a_1600_);
lean_dec(v_goal_1586_);
v___x_1616_ = lean_box(0);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1616_);
v___x_1618_ = v___x_1602_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1628_; 
lean_dec(v_goal_1586_);
v_a_1621_ = lean_ctor_get(v___x_1599_, 0);
v_isSharedCheck_1628_ = !lean_is_exclusive(v___x_1599_);
if (v_isSharedCheck_1628_ == 0)
{
v___x_1623_ = v___x_1599_;
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1599_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1628_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1626_; 
if (v_isShared_1624_ == 0)
{
v___x_1626_ = v___x_1623_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v_a_1621_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
return v___x_1626_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1629_, lean_object* v_target_1630_, lean_object* v_goal_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(v_scope_1629_, v_target_1630_, v_goal_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec_ref(v_target_1630_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(lean_object* v_scope_1645_, lean_object* v_goal_1646_, lean_object* v_target_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v___f_1660_; lean_object* v___x_1661_; 
lean_inc(v_goal_1646_);
v___f_1660_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1660_, 0, v_scope_1645_);
lean_closure_set(v___f_1660_, 1, v_target_1647_);
lean_closure_set(v___f_1660_, 2, v_goal_1646_);
v___x_1661_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1646_, v___f_1660_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1662_, lean_object* v_goal_1663_, lean_object* v_target_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_1662_, v_goal_1663_, v_target_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1677_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_1685_ = l_Lean_stringToMessageData(v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_1686_, lean_object* v_pre_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = l_Lean_Expr_cleanupAnnotations(v_pre_1687_);
v___x_1704_ = l_Lean_Expr_isApp(v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec_ref(v___x_1703_);
lean_dec(v_goal_1686_);
goto v___jp_1700_;
}
else
{
lean_object* v_arg_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_arg_1705_ = lean_ctor_get(v___x_1703_, 1);
lean_inc_ref(v_arg_1705_);
v___x_1706_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1703_);
v___x_1707_ = l_Lean_Expr_isApp(v___x_1706_);
if (v___x_1707_ == 0)
{
lean_dec_ref(v___x_1706_);
lean_dec_ref(v_arg_1705_);
lean_dec(v_goal_1686_);
goto v___jp_1700_;
}
else
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1706_);
v___x_1709_ = l_Lean_Expr_isApp(v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec_ref(v___x_1708_);
lean_dec_ref(v_arg_1705_);
lean_dec(v_goal_1686_);
goto v___jp_1700_;
}
else
{
lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1710_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1708_);
v___x_1711_ = l_Lean_Expr_isApp(v___x_1710_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_arg_1705_);
lean_dec(v_goal_1686_);
goto v___jp_1700_;
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1710_);
v___x_1713_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_1714_ = l_Lean_Expr_isConstOf(v___x_1712_, v___x_1713_);
lean_dec_ref(v___x_1712_);
if (v___x_1714_ == 0)
{
lean_dec_ref(v_arg_1705_);
lean_dec(v_goal_1686_);
goto v___jp_1700_;
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
v___x_1715_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1716_ = l_Lean_Expr_isAppOf(v_arg_1705_, v___x_1715_);
lean_dec_ref(v_arg_1705_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec(v_goal_1686_);
v___x_1717_ = lean_box(0);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
else
{
lean_object* v_backwardRules_1719_; lean_object* v_meetTop_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_backwardRules_1719_ = lean_ctor_get(v_a_1688_, 0);
v_meetTop_1720_ = lean_ctor_get(v_backwardRules_1719_, 8);
v___x_1721_ = lean_box(0);
lean_inc(v_goal_1686_);
lean_inc_ref(v_meetTop_1720_);
v___x_1722_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_1720_, v_goal_1686_, v___x_1721_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1749_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1725_ = v___x_1722_;
v_isShared_1726_ = v_isSharedCheck_1749_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_a_1723_);
lean_dec(v___x_1722_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1749_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; 
if (lean_obj_tag(v_a_1723_) == 1)
{
lean_object* v_mvarIds_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1748_; 
v_mvarIds_1736_ = lean_ctor_get(v_a_1723_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_a_1723_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1738_ = v_a_1723_;
v_isShared_1739_ = v_isSharedCheck_1748_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_mvarIds_1736_);
lean_dec(v_a_1723_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1748_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
if (lean_obj_tag(v_mvarIds_1736_) == 1)
{
lean_object* v_tail_1740_; 
v_tail_1740_ = lean_ctor_get(v_mvarIds_1736_, 1);
if (lean_obj_tag(v_tail_1740_) == 0)
{
lean_object* v_head_1741_; lean_object* v___x_1743_; 
lean_dec(v_goal_1686_);
v_head_1741_ = lean_ctor_get(v_mvarIds_1736_, 0);
lean_inc(v_head_1741_);
lean_dec_ref_known(v_mvarIds_1736_, 2);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 0, v_head_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_head_1741_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 0, v___x_1743_);
v___x_1745_ = v___x_1725_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1736_, 2);
lean_del_object(v___x_1738_);
lean_del_object(v___x_1725_);
v___y_1728_ = v_a_1695_;
v___y_1729_ = v_a_1696_;
v___y_1730_ = v_a_1697_;
v___y_1731_ = v_a_1698_;
goto v___jp_1727_;
}
}
else
{
lean_del_object(v___x_1738_);
lean_dec(v_mvarIds_1736_);
lean_del_object(v___x_1725_);
v___y_1728_ = v_a_1695_;
v___y_1729_ = v_a_1696_;
v___y_1730_ = v_a_1697_;
v___y_1731_ = v_a_1698_;
goto v___jp_1727_;
}
}
}
else
{
lean_del_object(v___x_1725_);
lean_dec(v_a_1723_);
v___y_1728_ = v_a_1695_;
v___y_1729_ = v_a_1696_;
v___y_1730_ = v_a_1697_;
v___y_1731_ = v_a_1698_;
goto v___jp_1727_;
}
v___jp_1727_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1733_, 0, v_goal_1686_);
v___x_1734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1732_);
lean_ctor_set(v___x_1734_, 1, v___x_1733_);
v___x_1735_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1734_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
return v___x_1735_;
}
}
}
else
{
lean_object* v_a_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1757_; 
lean_dec(v_goal_1686_);
v_a_1750_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1757_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1752_ = v___x_1722_;
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_a_1750_);
lean_dec(v___x_1722_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1757_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v___x_1755_; 
if (v_isShared_1753_ == 0)
{
v___x_1755_ = v___x_1752_;
goto v_reusejp_1754_;
}
else
{
lean_object* v_reuseFailAlloc_1756_; 
v_reuseFailAlloc_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1756_, 0, v_a_1750_);
v___x_1755_ = v_reuseFailAlloc_1756_;
goto v_reusejp_1754_;
}
v_reusejp_1754_:
{
return v___x_1755_;
}
}
}
}
}
}
}
}
}
v___jp_1700_:
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_1758_, lean_object* v_pre_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_1758_, v_pre_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec_ref(v_a_1765_);
lean_dec(v_a_1764_);
lean_dec_ref(v_a_1763_);
lean_dec(v_a_1762_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_1780_, lean_object* v_pre_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = l_Lean_Expr_cleanupAnnotations(v_pre_1781_);
v___x_1798_ = l_Lean_Expr_isApp(v___x_1797_);
if (v___x_1798_ == 0)
{
lean_dec_ref(v___x_1797_);
lean_dec(v_goal_1780_);
goto v___jp_1794_;
}
else
{
lean_object* v_arg_1799_; lean_object* v___x_1800_; uint8_t v___x_1801_; 
v_arg_1799_ = lean_ctor_get(v___x_1797_, 1);
lean_inc_ref(v_arg_1799_);
v___x_1800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1797_);
v___x_1801_ = l_Lean_Expr_isApp(v___x_1800_);
if (v___x_1801_ == 0)
{
lean_dec_ref(v___x_1800_);
lean_dec_ref(v_arg_1799_);
lean_dec(v_goal_1780_);
goto v___jp_1794_;
}
else
{
lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1802_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1800_);
v___x_1803_ = l_Lean_Expr_isApp(v___x_1802_);
if (v___x_1803_ == 0)
{
lean_dec_ref(v___x_1802_);
lean_dec_ref(v_arg_1799_);
lean_dec(v_goal_1780_);
goto v___jp_1794_;
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1802_);
v___x_1805_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_1806_ = l_Lean_Expr_isConstOf(v___x_1804_, v___x_1805_);
lean_dec_ref(v___x_1804_);
if (v___x_1806_ == 0)
{
lean_dec_ref(v_arg_1799_);
lean_dec(v_goal_1780_);
goto v___jp_1794_;
}
else
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_Expr_isTrue(v_arg_1799_);
if (v___x_1807_ == 0)
{
lean_object* v_backwardRules_1808_; lean_object* v_ofPropPreIntro_1809_; lean_object* v___x_1810_; 
v_backwardRules_1808_ = lean_ctor_get(v_a_1782_, 0);
v_ofPropPreIntro_1809_ = lean_ctor_get(v_backwardRules_1808_, 3);
lean_inc_ref(v_ofPropPreIntro_1809_);
v___x_1810_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_ofPropPreIntro_1809_, v_goal_1780_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1819_; 
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1819_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_a_1811_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
v_a_1820_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1810_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1810_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; 
lean_dec(v_goal_1780_);
v___x_1828_ = lean_box(0);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
}
}
}
v___jp_1794_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_box(0);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_1830_, lean_object* v_pre_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_1830_, v_pre_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(lean_object* v_goal_1845_, lean_object* v_00_u03b1_1846_, lean_object* v_pre_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Expr_isProp(v_00_u03b1_1846_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec(v_goal_1845_);
v___x_1861_ = lean_box(0);
v___x_1862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
return v___x_1862_;
}
else
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1864_ = l_Lean_Expr_isAppOf(v_pre_1847_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v_backwardRules_1865_; lean_object* v_propPreIntro_1866_; lean_object* v___x_1867_; 
v_backwardRules_1865_ = lean_ctor_get(v_a_1848_, 0);
v_propPreIntro_1866_ = lean_ctor_get(v_backwardRules_1865_, 2);
lean_inc_ref(v_propPreIntro_1866_);
v___x_1867_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_propPreIntro_1866_, v_goal_1845_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1876_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1870_ = v___x_1867_;
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_a_1868_);
lean_dec(v___x_1867_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1876_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_a_1868_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1872_);
v___x_1874_ = v___x_1870_;
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
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v___x_1867_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1867_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1867_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1867_);
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
else
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec(v_goal_1845_);
v___x_1885_ = lean_box(0);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_1887_, lean_object* v_00_u03b1_1888_, lean_object* v_pre_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_1887_, v_00_u03b1_1888_, v_pre_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec_ref(v_a_1895_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
lean_dec_ref(v_pre_1889_);
lean_dec_ref(v_00_u03b1_1888_);
return v_res_1902_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0));
v___x_1905_ = l_Lean_stringToMessageData(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = 0;
v___x_1912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3));
v___x_1913_ = l_Lean_MessageData_ofConstName(v___x_1912_, v___x_1911_);
return v___x_1913_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4);
v___x_1915_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
return v___x_1916_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6));
v___x_1919_ = l_Lean_stringToMessageData(v___x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7);
v___x_1921_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
lean_ctor_set(v___x_1922_, 1, v___x_1920_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(lean_object* v_goal_1923_, lean_object* v_pre_1924_, lean_object* v_target_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v___y_1939_; lean_object* v___y_1940_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; uint8_t v___x_1976_; 
lean_inc_ref(v_pre_1924_);
v___x_1976_ = l_Lean_Expr_isTrue(v_pre_1924_);
if (v___x_1976_ == 0)
{
v___y_1939_ = v_a_1931_;
v___y_1940_ = v_a_1932_;
v___y_1941_ = v_a_1933_;
v___y_1942_ = v_a_1934_;
v___y_1943_ = v_a_1935_;
v___y_1944_ = v_a_1936_;
goto v___jp_1938_;
}
else
{
lean_object* v_backwardRules_1977_; lean_object* v_truePreIntro_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_pre_1924_);
v_backwardRules_1977_ = lean_ctor_get(v_a_1926_, 0);
v_truePreIntro_1978_ = lean_ctor_get(v_backwardRules_1977_, 4);
v___x_1979_ = lean_box(0);
lean_inc_ref(v_truePreIntro_1978_);
v___x_1980_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_1978_, v_goal_1923_, v___x_1979_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2016_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_2016_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2016_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; 
if (lean_obj_tag(v_a_1981_) == 1)
{
lean_object* v_mvarIds_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2015_; 
v_mvarIds_2004_ = lean_ctor_get(v_a_1981_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2006_ = v_a_1981_;
v_isShared_2007_ = v_isSharedCheck_2015_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_mvarIds_2004_);
lean_dec(v_a_1981_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2015_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
if (lean_obj_tag(v_mvarIds_2004_) == 1)
{
lean_object* v_tail_2008_; 
v_tail_2008_ = lean_ctor_get(v_mvarIds_2004_, 1);
if (lean_obj_tag(v_tail_2008_) == 0)
{
lean_object* v___x_2010_; 
lean_dec_ref(v_target_1925_);
if (v_isShared_2007_ == 0)
{
v___x_2010_ = v___x_2006_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_mvarIds_2004_);
v___x_2010_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2010_);
v___x_2012_ = v___x_1983_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2004_, 2);
lean_del_object(v___x_2006_);
lean_del_object(v___x_1983_);
v___y_1986_ = v_a_1931_;
v___y_1987_ = v_a_1932_;
v___y_1988_ = v_a_1933_;
v___y_1989_ = v_a_1934_;
v___y_1990_ = v_a_1935_;
v___y_1991_ = v_a_1936_;
goto v___jp_1985_;
}
}
else
{
lean_del_object(v___x_2006_);
lean_dec(v_mvarIds_2004_);
lean_del_object(v___x_1983_);
v___y_1986_ = v_a_1931_;
v___y_1987_ = v_a_1932_;
v___y_1988_ = v_a_1933_;
v___y_1989_ = v_a_1934_;
v___y_1990_ = v_a_1935_;
v___y_1991_ = v_a_1936_;
goto v___jp_1985_;
}
}
}
else
{
lean_del_object(v___x_1983_);
lean_dec(v_a_1981_);
v___y_1986_ = v_a_1931_;
v___y_1987_ = v_a_1932_;
v___y_1988_ = v_a_1933_;
v___y_1989_ = v_a_1934_;
v___y_1990_ = v_a_1935_;
v___y_1991_ = v_a_1936_;
goto v___jp_1985_;
}
v___jp_1985_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2003_; 
v___x_1992_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8);
v___x_1993_ = l_Lean_indentExpr(v_target_1925_);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1994_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2003_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___x_2001_; 
if (v_isShared_1999_ == 0)
{
v___x_2001_ = v___x_1998_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
else
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref(v_target_1925_);
v_a_2017_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2019_ = v___x_1980_;
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_1980_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2024_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2022_; 
if (v_isShared_2020_ == 0)
{
v___x_2022_ = v___x_2019_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
}
v___jp_1938_:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(v_goal_1923_, v_target_1925_, v_pre_1924_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1967_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1948_ = v___x_1945_;
v_isShared_1949_ = v_isSharedCheck_1967_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1945_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1967_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
if (lean_obj_tag(v_a_1946_) == 1)
{
lean_object* v_val_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1962_; 
v_val_1950_ = lean_ctor_get(v_a_1946_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1946_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1952_ = v_a_1946_;
v_isShared_1953_ = v_isSharedCheck_1962_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_val_1950_);
lean_dec(v_a_1946_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1962_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_val_1950_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
if (v_isShared_1953_ == 0)
{
lean_ctor_set(v___x_1952_, 0, v___x_1955_);
v___x_1957_ = v___x_1952_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1957_);
v___x_1959_ = v___x_1948_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_dec(v_a_1946_);
v___x_1963_ = lean_box(0);
if (v_isShared_1949_ == 0)
{
lean_ctor_set(v___x_1948_, 0, v___x_1963_);
v___x_1965_ = v___x_1948_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_object* v_a_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1975_; 
v_a_1968_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1975_ == 0)
{
v___x_1970_ = v___x_1945_;
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_a_1968_);
lean_dec(v___x_1945_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1975_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1973_; 
if (v_isShared_1971_ == 0)
{
v___x_1973_ = v___x_1970_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_2025_, lean_object* v_pre_2026_, lean_object* v_target_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_, lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2025_, v_pre_2026_, v_target_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_, v_a_2037_, v_a_2038_);
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2037_);
lean_dec(v_a_2036_);
lean_dec_ref(v_a_2035_);
lean_dec(v_a_2034_);
lean_dec_ref(v_a_2033_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec(v_a_2029_);
lean_dec_ref(v_a_2028_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object* v_scope_2041_, lean_object* v_goal_2042_, lean_object* v_00_u03b1_2043_, lean_object* v_pre_2044_, lean_object* v_target_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v_g_2059_; lean_object* v_g_2066_; lean_object* v_h_2067_; lean_object* v___x_2085_; 
lean_inc_ref(v_pre_2044_);
lean_inc(v_goal_2042_);
v___x_2085_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_2042_, v_pre_2044_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
if (lean_obj_tag(v_a_2086_) == 1)
{
lean_object* v_val_2087_; 
lean_dec_ref(v_target_2045_);
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
v_val_2087_ = lean_ctor_get(v_a_2086_, 0);
lean_inc(v_val_2087_);
lean_dec_ref_known(v_a_2086_, 1);
v_g_2059_ = v_val_2087_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2088_; 
lean_dec(v_a_2086_);
lean_inc_ref(v_pre_2044_);
lean_inc(v_goal_2042_);
v___x_2088_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_2042_, v_pre_2044_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
if (lean_obj_tag(v_a_2089_) == 1)
{
lean_object* v_val_2090_; lean_object* v_fst_2091_; lean_object* v_snd_2092_; 
lean_dec_ref(v_target_2045_);
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
v_val_2090_ = lean_ctor_get(v_a_2089_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v_a_2089_, 1);
v_fst_2091_ = lean_ctor_get(v_val_2090_, 0);
lean_inc(v_fst_2091_);
v_snd_2092_ = lean_ctor_get(v_val_2090_, 1);
lean_inc(v_snd_2092_);
lean_dec(v_val_2090_);
v_g_2066_ = v_fst_2091_;
v_h_2067_ = v_snd_2092_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_a_2089_);
lean_inc(v_goal_2042_);
v___x_2093_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_2042_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref_known(v___x_2093_, 1);
if (lean_obj_tag(v_a_2094_) == 1)
{
lean_object* v_val_2095_; 
lean_dec_ref(v_target_2045_);
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
v_val_2095_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_a_2094_, 1);
v_g_2059_ = v_val_2095_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2096_; 
lean_dec(v_a_2094_);
lean_inc_ref(v_pre_2044_);
lean_inc(v_goal_2042_);
v___x_2096_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2042_, v_pre_2044_, v_target_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2134_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2134_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2134_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
if (lean_obj_tag(v_a_2097_) == 1)
{
lean_object* v_val_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
v_val_2101_ = lean_ctor_get(v_a_2097_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v_a_2097_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2103_ = v_a_2097_;
v_isShared_2104_ = v_isSharedCheck_2112_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_val_2101_);
lean_dec(v_a_2097_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2112_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_scope_2041_);
lean_ctor_set(v___x_2105_, 1, v_val_2101_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2109_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2107_);
v___x_2109_ = v___x_2099_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
else
{
lean_object* v___x_2113_; 
lean_del_object(v___x_2099_);
lean_dec(v_a_2097_);
v___x_2113_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_2042_, v_00_u03b1_2043_, v_pre_2044_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec_ref(v_pre_2044_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2125_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2125_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
if (lean_obj_tag(v_a_2114_) == 1)
{
lean_object* v_val_2118_; lean_object* v_fst_2119_; lean_object* v_snd_2120_; 
lean_del_object(v___x_2116_);
v_val_2118_ = lean_ctor_get(v_a_2114_, 0);
lean_inc(v_val_2118_);
lean_dec_ref_known(v_a_2114_, 1);
v_fst_2119_ = lean_ctor_get(v_val_2118_, 0);
lean_inc(v_fst_2119_);
v_snd_2120_ = lean_ctor_get(v_val_2118_, 1);
lean_inc(v_snd_2120_);
lean_dec(v_val_2118_);
v_g_2066_ = v_fst_2119_;
v_h_2067_ = v_snd_2120_;
goto v___jp_2065_;
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
lean_dec(v_a_2114_);
lean_dec_ref(v_scope_2041_);
v___x_2121_ = lean_box(0);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2121_);
v___x_2123_ = v___x_2116_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec_ref(v_scope_2041_);
v_a_2126_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2113_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2113_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
lean_dec_ref(v_scope_2041_);
v_a_2135_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2096_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2096_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec_ref(v_target_2045_);
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
lean_dec_ref(v_scope_2041_);
v_a_2143_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2093_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2093_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v_target_2045_);
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
lean_dec_ref(v_scope_2041_);
v_a_2151_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2088_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2088_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v_target_2045_);
lean_dec_ref(v_pre_2044_);
lean_dec(v_goal_2042_);
lean_dec_ref(v_scope_2041_);
v_a_2159_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2085_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2085_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
v___jp_2058_:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2060_ = lean_box(0);
v___x_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_g_2059_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_scope_2041_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
v___x_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
return v___x_2064_;
}
v___jp_2065_:
{
lean_object* v_specs_2068_; lean_object* v_jps_2069_; lean_object* v_nextDeclIdx_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2083_; 
v_specs_2068_ = lean_ctor_get(v_scope_2041_, 0);
v_jps_2069_ = lean_ctor_get(v_scope_2041_, 1);
v_nextDeclIdx_2070_ = lean_ctor_get(v_scope_2041_, 3);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_scope_2041_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_scope_2041_, 2);
lean_dec(v_unused_2084_);
v___x_2072_ = v_scope_2041_;
v_isShared_2073_ = v_isSharedCheck_2083_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_nextDeclIdx_2070_);
lean_inc(v_jps_2069_);
lean_inc(v_specs_2068_);
lean_dec(v_scope_2041_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2083_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2074_, 0, v_h_2067_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 2, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_specs_2068_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_jps_2069_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_nextDeclIdx_2070_);
v___x_2076_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2078_, 0, v_g_2066_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2076_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2167_ = _args[0];
lean_object* v_goal_2168_ = _args[1];
lean_object* v_00_u03b1_2169_ = _args[2];
lean_object* v_pre_2170_ = _args[3];
lean_object* v_target_2171_ = _args[4];
lean_object* v_a_2172_ = _args[5];
lean_object* v_a_2173_ = _args[6];
lean_object* v_a_2174_ = _args[7];
lean_object* v_a_2175_ = _args[8];
lean_object* v_a_2176_ = _args[9];
lean_object* v_a_2177_ = _args[10];
lean_object* v_a_2178_ = _args[11];
lean_object* v_a_2179_ = _args[12];
lean_object* v_a_2180_ = _args[13];
lean_object* v_a_2181_ = _args[14];
lean_object* v_a_2182_ = _args[15];
lean_object* v_a_2183_ = _args[16];
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_2167_, v_goal_2168_, v_00_u03b1_2169_, v_pre_2170_, v_target_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
lean_dec(v_a_2176_);
lean_dec_ref(v_a_2175_);
lean_dec(v_a_2174_);
lean_dec(v_a_2173_);
lean_dec_ref(v_a_2172_);
lean_dec_ref(v_00_u03b1_2169_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2185_, lean_object* v_a_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___y_2195_; lean_object* v___x_2198_; uint8_t v_debug_2199_; 
v___x_2198_ = lean_st_ref_get(v___y_2188_);
v_debug_2199_ = lean_ctor_get_uint8(v___x_2198_, sizeof(void*)*10);
lean_dec(v___x_2198_);
if (v_debug_2199_ == 0)
{
v___y_2195_ = v___y_2188_;
goto v___jp_2194_;
}
else
{
lean_object* v___x_2200_; 
lean_inc_ref(v_f_2185_);
v___x_2200_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2185_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2201_; 
lean_dec_ref_known(v___x_2200_, 1);
lean_inc_ref(v_a_2186_);
v___x_2201_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2186_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_dec_ref_known(v___x_2201_, 1);
v___y_2195_ = v___y_2188_;
goto v___jp_2194_;
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v_a_2186_);
lean_dec_ref(v_f_2185_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2217_; 
lean_dec_ref(v_a_2186_);
lean_dec_ref(v_f_2185_);
v_a_2210_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2212_ = v___x_2200_;
v_isShared_2213_ = v_isSharedCheck_2217_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2200_);
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
v___jp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = l_Lean_Expr_app___override(v_f_2185_, v_a_2186_);
v___x_2197_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2196_, v___y_2195_);
return v___x_2197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2218_, lean_object* v_a_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2218_, v_a_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object* v_args_2228_, lean_object* v_endIdx_2229_, lean_object* v_b_2230_, lean_object* v_i_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_nat_dec_le(v_endIdx_2229_, v_i_2231_);
if (v___x_2244_ == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = l_Lean_instInhabitedExpr;
v___x_2246_ = lean_array_get_borrowed(v___x_2245_, v_args_2228_, v_i_2231_);
lean_inc(v___x_2246_);
v___x_2247_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2230_, v___x_2246_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_add(v_i_2231_, v___x_2249_);
lean_dec(v_i_2231_);
v_b_2230_ = v_a_2248_;
v_i_2231_ = v___x_2250_;
goto _start;
}
else
{
lean_dec(v_i_2231_);
return v___x_2247_;
}
}
else
{
lean_object* v___x_2252_; 
lean_dec(v_i_2231_);
v___x_2252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2252_, 0, v_b_2230_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object* v_args_2253_, lean_object* v_endIdx_2254_, lean_object* v_b_2255_, lean_object* v_i_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2253_, v_endIdx_2254_, v_b_2255_, v_i_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v_endIdx_2254_);
lean_dec_ref(v_args_2253_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object* v_f_2270_, lean_object* v_args_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2284_ = lean_unsigned_to_nat(0u);
v___x_2285_ = lean_array_get_size(v_args_2271_);
v___x_2286_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2271_, v___x_2285_, v_f_2270_, v___x_2284_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object* v_f_2287_, lean_object* v_args_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_2287_, v_args_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec_ref(v_args_2288_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_2302_, lean_object* v_info_2303_, lean_object* v_prog_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_head_2317_; lean_object* v_args_2318_; lean_object* v_excessArgs_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_head_2317_ = lean_ctor_get(v_info_2303_, 0);
lean_inc_ref(v_head_2317_);
v_args_2318_ = lean_ctor_get(v_info_2303_, 1);
lean_inc_ref(v_args_2318_);
v_excessArgs_2319_ = lean_ctor_get(v_info_2303_, 2);
lean_inc_ref(v_excessArgs_2319_);
lean_dec_ref(v_info_2303_);
v___x_2320_ = lean_unsigned_to_nat(7u);
v___x_2321_ = lean_array_set(v_args_2318_, v___x_2320_, v_prog_2304_);
v___x_2322_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2317_, v___x_2321_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
lean_dec_ref(v___x_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2323_, v_excessArgs_2319_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
lean_dec_ref(v_excessArgs_2319_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
lean_inc(v_goal_2302_);
v___x_2326_ = l_Lean_MVarId_getType(v_goal_2302_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v_dummy_2328_; lean_object* v_nargs_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc_n(v_a_2327_, 2);
lean_dec_ref_known(v___x_2326_, 1);
v_dummy_2328_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_2329_ = l_Lean_Expr_getAppNumArgs(v_a_2327_);
lean_inc(v_nargs_2329_);
v___x_2330_ = lean_mk_array(v_nargs_2329_, v_dummy_2328_);
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_sub(v_nargs_2329_, v___x_2331_);
lean_dec(v_nargs_2329_);
v___x_2333_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2327_, v___x_2330_, v___x_2332_);
v___x_2334_ = l_Lean_Expr_getAppFn(v_a_2327_);
lean_dec(v_a_2327_);
v___x_2335_ = lean_array_get_size(v___x_2333_);
v___x_2336_ = lean_nat_sub(v___x_2335_, v___x_2331_);
v___x_2337_ = lean_array_set(v___x_2333_, v___x_2336_, v_a_2325_);
lean_dec(v___x_2336_);
v___x_2338_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2334_, v___x_2337_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
lean_dec_ref(v___x_2337_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_2302_, v_a_2339_, v_a_2312_, v_a_2313_, v_a_2314_, v_a_2315_);
return v___x_2340_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_goal_2302_);
v_a_2341_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2338_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2338_);
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
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2325_);
lean_dec(v_goal_2302_);
v_a_2349_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2326_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2326_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec(v_goal_2302_);
v_a_2357_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2324_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2324_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v_excessArgs_2319_);
lean_dec(v_goal_2302_);
v_a_2365_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2322_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2322_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2373_, lean_object* v_info_2374_, lean_object* v_prog_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2373_, v_info_2374_, v_prog_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
lean_dec(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(lean_object* v_f_2389_, lean_object* v_a_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2389_, v_a_2390_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2404_, lean_object* v_a_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(v_f_2404_, v_a_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2419_, lean_object* v_start_2420_, lean_object* v_b_2421_, lean_object* v_i_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_nat_dec_le(v_i_2422_, v_start_2420_);
if (v___x_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v_i_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2431_ = lean_unsigned_to_nat(1u);
v_i_2432_ = lean_nat_sub(v_i_2422_, v___x_2431_);
lean_dec(v_i_2422_);
v___x_2433_ = l_Lean_instInhabitedExpr;
v___x_2434_ = lean_array_get_borrowed(v___x_2433_, v_revArgs_2419_, v_i_2432_);
lean_inc(v___x_2434_);
v___x_2435_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2421_, v___x_2434_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_a_2436_);
lean_dec_ref_known(v___x_2435_, 1);
v_b_2421_ = v_a_2436_;
v_i_2422_ = v_i_2432_;
goto _start;
}
else
{
lean_dec(v_i_2432_);
return v___x_2435_;
}
}
else
{
lean_object* v___x_2438_; 
lean_dec(v_i_2422_);
v___x_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2438_, 0, v_b_2421_);
return v___x_2438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2439_, lean_object* v_start_2440_, lean_object* v_b_2441_, lean_object* v_i_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2439_, v_start_2440_, v_b_2441_, v_i_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_start_2440_);
lean_dec_ref(v_revArgs_2439_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2451_, lean_object* v_revArgs_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = lean_array_get_size(v_revArgs_2452_);
v___x_2467_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2452_, v___x_2465_, v_f_2451_, v___x_2466_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_2468_, lean_object* v_revArgs_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_f_2468_, v_revArgs_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec_ref(v_revArgs_2469_);
return v_res_2482_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0));
v___x_2485_ = l_Lean_stringToMessageData(v___x_2484_);
return v___x_2485_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2));
v___x_2488_ = l_Lean_stringToMessageData(v___x_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object* v_goal_2489_, lean_object* v_info_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2490_);
v___x_2504_ = l_Lean_Expr_getAppFn(v___x_2503_);
if (lean_obj_tag(v___x_2504_) == 8)
{
lean_object* v_declName_2505_; lean_object* v_type_2506_; lean_object* v_value_2507_; lean_object* v_body_2508_; uint8_t v_nondep_2509_; lean_object* v___x_2510_; 
v_declName_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc_n(v_declName_2505_, 2);
v_type_2506_ = lean_ctor_get(v___x_2504_, 1);
lean_inc_ref(v_type_2506_);
v_value_2507_ = lean_ctor_get(v___x_2504_, 2);
lean_inc_ref(v_value_2507_);
v_body_2508_ = lean_ctor_get(v___x_2504_, 3);
lean_inc_ref(v_body_2508_);
v_nondep_2509_ = lean_ctor_get_uint8(v___x_2504_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_2504_, 4);
v___x_2510_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_2505_, v_value_2507_, v_a_2491_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v_appArgs_2513_; lean_object* v___y_2515_; lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; lean_object* v___y_2525_; uint8_t v___x_2567_; 
lean_dec_ref_known(v___x_2510_, 1);
v___x_2511_ = l_Lean_Expr_getAppNumArgs(v___x_2503_);
v___x_2512_ = lean_mk_empty_array_with_capacity(v___x_2511_);
lean_dec(v___x_2511_);
v_appArgs_2513_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2503_, v___x_2512_);
v___x_2567_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_2507_);
if (v___x_2567_ == 0)
{
lean_object* v_options_2568_; lean_object* v_inheritedTraceOptions_2569_; uint8_t v_hasTrace_2570_; uint8_t v___x_2571_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; 
v_options_2568_ = lean_ctor_get(v_a_2500_, 2);
v_inheritedTraceOptions_2569_ = lean_ctor_get(v_a_2500_, 13);
v_hasTrace_2570_ = lean_ctor_get_uint8(v_options_2568_, sizeof(void*)*1);
v___x_2571_ = 1;
if (v_hasTrace_2570_ == 0)
{
v___y_2573_ = v_a_2491_;
v___y_2574_ = v_a_2492_;
v___y_2575_ = v_a_2493_;
v___y_2576_ = v_a_2494_;
v___y_2577_ = v_a_2495_;
v___y_2578_ = v_a_2496_;
v___y_2579_ = v_a_2497_;
v___y_2580_ = v_a_2498_;
v___y_2581_ = v_a_2499_;
v___y_2582_ = v_a_2500_;
v___y_2583_ = v_a_2501_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v___x_2682_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2683_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2684_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2569_, v_options_2568_, v___x_2683_);
if (v___x_2684_ == 0)
{
v___y_2573_ = v_a_2491_;
v___y_2574_ = v_a_2492_;
v___y_2575_ = v_a_2493_;
v___y_2576_ = v_a_2494_;
v___y_2577_ = v_a_2495_;
v___y_2578_ = v_a_2496_;
v___y_2579_ = v_a_2497_;
v___y_2580_ = v_a_2498_;
v___y_2581_ = v_a_2499_;
v___y_2582_ = v_a_2500_;
v___y_2583_ = v_a_2501_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2685_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_2505_);
v___x_2686_ = l_Lean_MessageData_ofName(v_declName_2505_);
v___x_2687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2685_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2682_, v___x_2687_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_dec_ref_known(v___x_2688_, 1);
v___y_2573_ = v_a_2491_;
v___y_2574_ = v_a_2492_;
v___y_2575_ = v_a_2493_;
v___y_2576_ = v_a_2494_;
v___y_2577_ = v_a_2495_;
v___y_2578_ = v_a_2496_;
v___y_2579_ = v_a_2497_;
v___y_2580_ = v_a_2498_;
v___y_2581_ = v_a_2499_;
v___y_2582_ = v_a_2500_;
v___y_2583_ = v_a_2501_;
goto v___jp_2572_;
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v_appArgs_2513_);
lean_dec_ref(v_body_2508_);
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2688_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2688_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2688_);
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
v___jp_2572_:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_body_2508_, v_appArgs_2513_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec_ref(v_appArgs_2513_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_head_2586_; lean_object* v_args_2587_; lean_object* v_excessArgs_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v_head_2586_ = lean_ctor_get(v_info_2490_, 0);
lean_inc_ref(v_head_2586_);
v_args_2587_ = lean_ctor_get(v_info_2490_, 1);
lean_inc_ref(v_args_2587_);
v_excessArgs_2588_ = lean_ctor_get(v_info_2490_, 2);
lean_inc_ref(v_excessArgs_2588_);
lean_dec_ref(v_info_2490_);
v___x_2589_ = lean_unsigned_to_nat(7u);
v___x_2590_ = lean_array_set(v_args_2587_, v___x_2589_, v_a_2585_);
v___x_2591_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2586_, v___x_2590_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec_ref(v___x_2590_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2593_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v___x_2593_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2592_, v_excessArgs_2588_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec_ref(v_excessArgs_2588_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
lean_inc(v_goal_2489_);
v___x_2595_ = l_Lean_MVarId_getType(v_goal_2489_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v_dummy_2597_; lean_object* v_nargs_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc_n(v_a_2596_, 2);
lean_dec_ref_known(v___x_2595_, 1);
v_dummy_2597_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_2598_ = l_Lean_Expr_getAppNumArgs(v_a_2596_);
lean_inc(v_nargs_2598_);
v___x_2599_ = lean_mk_array(v_nargs_2598_, v_dummy_2597_);
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = lean_nat_sub(v_nargs_2598_, v___x_2600_);
lean_dec(v_nargs_2598_);
v___x_2602_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2596_, v___x_2599_, v___x_2601_);
v___x_2603_ = l_Lean_Expr_getAppFn(v_a_2596_);
lean_dec(v_a_2596_);
v___x_2604_ = lean_array_get_size(v___x_2602_);
v___x_2605_ = lean_nat_sub(v___x_2604_, v___x_2600_);
v___x_2606_ = lean_array_set(v___x_2602_, v___x_2605_, v_a_2594_);
lean_dec(v___x_2605_);
v___x_2607_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2603_, v___x_2606_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec_ref(v___x_2606_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_a_2608_);
lean_dec_ref_known(v___x_2607_, 1);
v___x_2609_ = l_Lean_Expr_letE___override(v_declName_2505_, v_type_2506_, v_value_2507_, v_a_2608_, v_nondep_2509_);
v___x_2610_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_2489_, v___x_2609_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2613_ = l_Lean_Meta_Sym_intros(v_a_2611_, v___x_2612_, v___x_2571_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2625_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2616_ = v___x_2613_;
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2625_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
if (lean_obj_tag(v_a_2614_) == 1)
{
lean_object* v_mvarId_2618_; lean_object* v___x_2619_; lean_object* v___x_2621_; 
v_mvarId_2618_ = lean_ctor_get(v_a_2614_, 1);
lean_inc(v_mvarId_2618_);
lean_dec_ref_known(v_a_2614_, 2);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_mvarId_2618_);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v___x_2619_);
v___x_2621_ = v___x_2616_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_del_object(v___x_2616_);
lean_dec(v_a_2614_);
v___x_2623_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1);
v___x_2624_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2623_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2624_;
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2613_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2613_);
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
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
v_a_2634_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2610_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2610_);
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
else
{
lean_object* v_a_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec(v_goal_2489_);
v_a_2642_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2607_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_a_2642_);
lean_dec(v___x_2607_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_a_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec(v_a_2594_);
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec(v_goal_2489_);
v_a_2650_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2595_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2595_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec(v_goal_2489_);
v_a_2658_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2593_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2593_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v_excessArgs_2588_);
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec(v_goal_2489_);
v_a_2666_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2591_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2591_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v_a_2674_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2584_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2584_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_object* v_options_2697_; uint8_t v_hasTrace_2698_; 
lean_dec_ref(v_type_2506_);
v_options_2697_ = lean_ctor_get(v_a_2500_, 2);
v_hasTrace_2698_ = lean_ctor_get_uint8(v_options_2697_, sizeof(void*)*1);
if (v_hasTrace_2698_ == 0)
{
lean_dec(v_declName_2505_);
v___y_2515_ = v_a_2491_;
v___y_2516_ = v_a_2492_;
v___y_2517_ = v_a_2493_;
v___y_2518_ = v_a_2494_;
v___y_2519_ = v_a_2495_;
v___y_2520_ = v_a_2496_;
v___y_2521_ = v_a_2497_;
v___y_2522_ = v_a_2498_;
v___y_2523_ = v_a_2499_;
v___y_2524_ = v_a_2500_;
v___y_2525_ = v_a_2501_;
goto v___jp_2514_;
}
else
{
lean_object* v_inheritedTraceOptions_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_inheritedTraceOptions_2699_ = lean_ctor_get(v_a_2500_, 13);
v___x_2700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2701_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2699_, v_options_2697_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_dec(v_declName_2505_);
v___y_2515_ = v_a_2491_;
v___y_2516_ = v_a_2492_;
v___y_2517_ = v_a_2493_;
v___y_2518_ = v_a_2494_;
v___y_2519_ = v_a_2495_;
v___y_2520_ = v_a_2496_;
v___y_2521_ = v_a_2497_;
v___y_2522_ = v_a_2498_;
v___y_2523_ = v_a_2499_;
v___y_2524_ = v_a_2500_;
v___y_2525_ = v_a_2501_;
goto v___jp_2514_;
}
else
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_2704_ = l_Lean_MessageData_ofName(v_declName_2505_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2700_, v___x_2705_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_dec_ref_known(v___x_2706_, 1);
v___y_2515_ = v_a_2491_;
v___y_2516_ = v_a_2492_;
v___y_2517_ = v_a_2493_;
v___y_2518_ = v_a_2494_;
v___y_2519_ = v_a_2495_;
v___y_2520_ = v_a_2496_;
v___y_2521_ = v_a_2497_;
v___y_2522_ = v_a_2498_;
v___y_2523_ = v_a_2499_;
v___y_2524_ = v_a_2500_;
v___y_2525_ = v_a_2501_;
goto v___jp_2514_;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v_appArgs_2513_);
lean_dec_ref(v_body_2508_);
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2706_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2706_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2706_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
v___jp_2514_:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = lean_unsigned_to_nat(1u);
v___x_2527_ = lean_mk_empty_array_with_capacity(v___x_2526_);
v___x_2528_ = lean_array_push(v___x_2527_, v_value_2507_);
v___x_2529_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_body_2508_, v___x_2528_, v___y_2521_);
lean_dec_ref(v___x_2528_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2531_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
lean_inc(v_a_2530_);
lean_dec_ref_known(v___x_2529_, 1);
v___x_2531_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_a_2530_, v_appArgs_2513_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec_ref(v_appArgs_2513_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2533_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
v___x_2533_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2489_, v_info_2490_, v_a_2532_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2542_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2536_ = v___x_2533_;
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_a_2534_);
lean_dec(v___x_2533_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2542_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
v___x_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2538_, 0, v_a_2534_);
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 0, v___x_2538_);
v___x_2540_ = v___x_2536_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_a_2543_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2533_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2533_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v_a_2551_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2531_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2531_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec_ref(v_appArgs_2513_);
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v_a_2559_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2529_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2529_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v_body_2508_);
lean_dec_ref(v_value_2507_);
lean_dec_ref(v_type_2506_);
lean_dec(v_declName_2505_);
lean_dec_ref(v___x_2503_);
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v_a_2715_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2510_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2510_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v___x_2723_; lean_object* v___x_2724_; 
lean_dec_ref(v___x_2504_);
lean_dec_ref(v___x_2503_);
lean_dec_ref(v_info_2490_);
lean_dec(v_goal_2489_);
v___x_2723_ = lean_box(0);
v___x_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
return v___x_2724_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object* v_goal_2725_, lean_object* v_info_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_2725_, v_info_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_, v_a_2736_, v_a_2737_);
lean_dec(v_a_2737_);
lean_dec_ref(v_a_2736_);
lean_dec(v_a_2735_);
lean_dec_ref(v_a_2734_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_a_2730_);
lean_dec(v_a_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_a_2727_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_2740_, lean_object* v_start_2741_, lean_object* v_b_2742_, lean_object* v_i_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2740_, v_start_2741_, v_b_2742_, v_i_2743_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_2757_, lean_object* v_start_2758_, lean_object* v_b_2759_, lean_object* v_i_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_2757_, v_start_2758_, v_b_2759_, v_i_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v_start_2758_);
lean_dec_ref(v_revArgs_2757_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_2774_, lean_object* v_b_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
if (lean_obj_tag(v_as_x27_2774_) == 0)
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_b_2775_);
return v___x_2785_;
}
else
{
lean_object* v_head_2786_; lean_object* v_tail_2787_; lean_object* v___x_2788_; 
v_head_2786_ = lean_ctor_get(v_as_x27_2774_, 0);
v_tail_2787_ = lean_ctor_get(v_as_x27_2774_, 1);
lean_inc(v_head_2786_);
v___x_2788_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_head_2786_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
switch(lean_obj_tag(v_a_2789_))
{
case 0:
{
lean_object* v___x_2790_; 
lean_inc(v_head_2786_);
v___x_2790_ = lean_array_push(v_b_2775_, v_head_2786_);
v_as_x27_2774_ = v_tail_2787_;
v_b_2775_ = v___x_2790_;
goto _start;
}
case 1:
{
v_as_x27_2774_ = v_tail_2787_;
goto _start;
}
default: 
{
lean_object* v_mvarId_2793_; lean_object* v___x_2794_; 
v_mvarId_2793_ = lean_ctor_get(v_a_2789_, 0);
lean_inc(v_mvarId_2793_);
lean_dec_ref_known(v_a_2789_, 1);
v___x_2794_ = lean_array_push(v_b_2775_, v_mvarId_2793_);
v_as_x27_2774_ = v_tail_2787_;
v_b_2775_ = v___x_2794_;
goto _start;
}
}
}
else
{
lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2803_; 
lean_dec_ref(v_b_2775_);
v_a_2796_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2798_ = v___x_2788_;
v_isShared_2799_ = v_isSharedCheck_2803_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_dec(v___x_2788_);
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
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_2804_, lean_object* v_b_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_2804_, v_b_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
lean_dec_ref(v___y_2810_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec(v_as_x27_2804_);
return v_res_2815_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0));
v___x_2818_ = l_Lean_stringToMessageData(v___x_2817_);
return v___x_2818_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2));
v___x_2821_ = l_Lean_stringToMessageData(v___x_2820_);
return v___x_2821_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4(void){
_start:
{
uint8_t v___x_2822_; uint64_t v___x_2823_; 
v___x_2822_ = 2;
v___x_2823_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object* v_goal_2824_, lean_object* v_info_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_, lean_object* v_a_2835_, lean_object* v_a_2836_){
_start:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; 
v___x_2838_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2825_);
lean_inc_ref(v___x_2838_);
v___x_2839_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_2838_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_3013_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2842_ = v___x_2839_;
v_isShared_2843_ = v_isSharedCheck_3013_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2839_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_3013_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
if (lean_obj_tag(v_a_2840_) == 1)
{
lean_object* v_val_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_3008_; 
lean_del_object(v___x_2842_);
v_val_2844_ = lean_ctor_get(v_a_2840_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_a_2840_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2846_ = v_a_2840_;
v_isShared_2847_ = v_isSharedCheck_3008_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_val_2844_);
lean_dec(v_a_2840_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_3008_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2854_; lean_object* v___y_2855_; lean_object* v___y_2856_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___y_2859_; 
if (lean_obj_tag(v_val_2844_) == 2)
{
lean_object* v___x_2916_; uint8_t v_foApprox_2917_; uint8_t v_ctxApprox_2918_; uint8_t v_quasiPatternApprox_2919_; uint8_t v_constApprox_2920_; uint8_t v_isDefEqStuckEx_2921_; uint8_t v_unificationHints_2922_; uint8_t v_proofIrrelevance_2923_; uint8_t v_assignSyntheticOpaque_2924_; uint8_t v_offsetCnstrs_2925_; uint8_t v_etaStruct_2926_; uint8_t v_univApprox_2927_; uint8_t v_iota_2928_; uint8_t v_beta_2929_; uint8_t v_proj_2930_; uint8_t v_zeta_2931_; uint8_t v_zetaDelta_2932_; uint8_t v_zetaUnused_2933_; uint8_t v_zetaHave_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_3007_; 
v___x_2916_ = l_Lean_Meta_Context_config(v_a_2833_);
v_foApprox_2917_ = lean_ctor_get_uint8(v___x_2916_, 0);
v_ctxApprox_2918_ = lean_ctor_get_uint8(v___x_2916_, 1);
v_quasiPatternApprox_2919_ = lean_ctor_get_uint8(v___x_2916_, 2);
v_constApprox_2920_ = lean_ctor_get_uint8(v___x_2916_, 3);
v_isDefEqStuckEx_2921_ = lean_ctor_get_uint8(v___x_2916_, 4);
v_unificationHints_2922_ = lean_ctor_get_uint8(v___x_2916_, 5);
v_proofIrrelevance_2923_ = lean_ctor_get_uint8(v___x_2916_, 6);
v_assignSyntheticOpaque_2924_ = lean_ctor_get_uint8(v___x_2916_, 7);
v_offsetCnstrs_2925_ = lean_ctor_get_uint8(v___x_2916_, 8);
v_etaStruct_2926_ = lean_ctor_get_uint8(v___x_2916_, 10);
v_univApprox_2927_ = lean_ctor_get_uint8(v___x_2916_, 11);
v_iota_2928_ = lean_ctor_get_uint8(v___x_2916_, 12);
v_beta_2929_ = lean_ctor_get_uint8(v___x_2916_, 13);
v_proj_2930_ = lean_ctor_get_uint8(v___x_2916_, 14);
v_zeta_2931_ = lean_ctor_get_uint8(v___x_2916_, 15);
v_zetaDelta_2932_ = lean_ctor_get_uint8(v___x_2916_, 16);
v_zetaUnused_2933_ = lean_ctor_get_uint8(v___x_2916_, 17);
v_zetaHave_2934_ = lean_ctor_get_uint8(v___x_2916_, 18);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2936_ = v___x_2916_;
v_isShared_2937_ = v_isSharedCheck_3007_;
goto v_resetjp_2935_;
}
else
{
lean_dec(v___x_2916_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_3007_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
uint8_t v_trackZetaDelta_2938_; lean_object* v_zetaDeltaSet_2939_; lean_object* v_lctx_2940_; lean_object* v_localInstances_2941_; lean_object* v_defEqCtx_x3f_2942_; lean_object* v_synthPendingDepth_2943_; lean_object* v_canUnfold_x3f_2944_; uint8_t v_univApprox_2945_; uint8_t v_inTypeClassResolution_2946_; uint8_t v_cacheInferType_2947_; uint8_t v___x_2948_; lean_object* v_config_2950_; 
v_trackZetaDelta_2938_ = lean_ctor_get_uint8(v_a_2833_, sizeof(void*)*7);
v_zetaDeltaSet_2939_ = lean_ctor_get(v_a_2833_, 1);
v_lctx_2940_ = lean_ctor_get(v_a_2833_, 2);
v_localInstances_2941_ = lean_ctor_get(v_a_2833_, 3);
v_defEqCtx_x3f_2942_ = lean_ctor_get(v_a_2833_, 4);
v_synthPendingDepth_2943_ = lean_ctor_get(v_a_2833_, 5);
v_canUnfold_x3f_2944_ = lean_ctor_get(v_a_2833_, 6);
v_univApprox_2945_ = lean_ctor_get_uint8(v_a_2833_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2946_ = lean_ctor_get_uint8(v_a_2833_, sizeof(void*)*7 + 2);
v_cacheInferType_2947_ = lean_ctor_get_uint8(v_a_2833_, sizeof(void*)*7 + 3);
v___x_2948_ = 2;
if (v_isShared_2937_ == 0)
{
v_config_2950_ = v___x_2936_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 0, v_foApprox_2917_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 1, v_ctxApprox_2918_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 2, v_quasiPatternApprox_2919_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 3, v_constApprox_2920_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 4, v_isDefEqStuckEx_2921_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 5, v_unificationHints_2922_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 6, v_proofIrrelevance_2923_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 7, v_assignSyntheticOpaque_2924_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 8, v_offsetCnstrs_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 10, v_etaStruct_2926_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 11, v_univApprox_2927_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 12, v_iota_2928_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 13, v_beta_2929_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 14, v_proj_2930_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 15, v_zeta_2931_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 16, v_zetaDelta_2932_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 17, v_zetaUnused_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_3006_, 18, v_zetaHave_2934_);
v_config_2950_ = v_reuseFailAlloc_3006_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
uint64_t v___x_2951_; uint64_t v___x_2952_; uint64_t v___x_2953_; uint64_t v___x_2954_; uint64_t v___x_2955_; uint64_t v_key_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
lean_ctor_set_uint8(v_config_2950_, 9, v___x_2948_);
v___x_2951_ = l_Lean_Meta_Context_configKey(v_a_2833_);
v___x_2952_ = 3ULL;
v___x_2953_ = lean_uint64_shift_right(v___x_2951_, v___x_2952_);
v___x_2954_ = lean_uint64_shift_left(v___x_2953_, v___x_2952_);
v___x_2955_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4);
v_key_2956_ = lean_uint64_lor(v___x_2954_, v___x_2955_);
v___x_2957_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2957_, 0, v_config_2950_);
lean_ctor_set_uint64(v___x_2957_, sizeof(void*)*1, v_key_2956_);
lean_inc(v_canUnfold_x3f_2944_);
lean_inc(v_synthPendingDepth_2943_);
lean_inc(v_defEqCtx_x3f_2942_);
lean_inc_ref(v_localInstances_2941_);
lean_inc_ref(v_lctx_2940_);
lean_inc(v_zetaDeltaSet_2939_);
v___x_2958_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
lean_ctor_set(v___x_2958_, 1, v_zetaDeltaSet_2939_);
lean_ctor_set(v___x_2958_, 2, v_lctx_2940_);
lean_ctor_set(v___x_2958_, 3, v_localInstances_2941_);
lean_ctor_set(v___x_2958_, 4, v_defEqCtx_x3f_2942_);
lean_ctor_set(v___x_2958_, 5, v_synthPendingDepth_2943_);
lean_ctor_set(v___x_2958_, 6, v_canUnfold_x3f_2944_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*7, v_trackZetaDelta_2938_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*7 + 1, v_univApprox_2945_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2946_);
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*7 + 3, v_cacheInferType_2947_);
v___x_2959_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_2838_, v___x_2958_, v_a_2834_, v_a_2835_, v_a_2836_);
lean_dec_ref_known(v___x_2958_, 7);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
if (lean_obj_tag(v_a_2960_) == 1)
{
lean_object* v_val_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2997_; 
lean_dec_ref_known(v_val_2844_, 1);
lean_del_object(v___x_2846_);
lean_dec_ref(v___x_2838_);
v_val_2961_ = lean_ctor_get(v_a_2960_, 0);
v_isSharedCheck_2997_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_2997_ == 0)
{
v___x_2963_ = v_a_2960_;
v_isShared_2964_ = v_isSharedCheck_2997_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_val_2961_);
lean_dec(v_a_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2997_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2961_, v_a_2832_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v___x_2967_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2824_, v_info_2825_, v_a_2966_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_, v_a_2834_, v_a_2835_, v_a_2836_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2980_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2980_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2980_ == 0)
{
v___x_2970_ = v___x_2967_;
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2967_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2980_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v_a_2968_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2973_);
v___x_2975_ = v___x_2963_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2979_; 
v_reuseFailAlloc_2979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2979_, 0, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2979_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2977_; 
if (v_isShared_2971_ == 0)
{
lean_ctor_set(v___x_2970_, 0, v___x_2975_);
v___x_2977_ = v___x_2970_;
goto v_reusejp_2976_;
}
else
{
lean_object* v_reuseFailAlloc_2978_; 
v_reuseFailAlloc_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2978_, 0, v___x_2975_);
v___x_2977_ = v_reuseFailAlloc_2978_;
goto v_reusejp_2976_;
}
v_reusejp_2976_:
{
return v___x_2977_;
}
}
}
}
else
{
lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_del_object(v___x_2963_);
v_a_2981_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2967_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2967_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_del_object(v___x_2963_);
lean_dec_ref(v_info_2825_);
lean_dec(v_goal_2824_);
v_a_2989_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2965_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2965_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
else
{
lean_dec(v_a_2960_);
v___y_2849_ = v_a_2826_;
v___y_2850_ = v_a_2827_;
v___y_2851_ = v_a_2828_;
v___y_2852_ = v_a_2829_;
v___y_2853_ = v_a_2830_;
v___y_2854_ = v_a_2831_;
v___y_2855_ = v_a_2832_;
v___y_2856_ = v_a_2833_;
v___y_2857_ = v_a_2834_;
v___y_2858_ = v_a_2835_;
v___y_2859_ = v_a_2836_;
goto v___jp_2848_;
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_dec_ref_known(v_val_2844_, 1);
lean_del_object(v___x_2846_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v_info_2825_);
lean_dec(v_goal_2824_);
v_a_2998_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2959_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2959_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
}
}
else
{
v___y_2849_ = v_a_2826_;
v___y_2850_ = v_a_2827_;
v___y_2851_ = v_a_2828_;
v___y_2852_ = v_a_2829_;
v___y_2853_ = v_a_2830_;
v___y_2854_ = v_a_2831_;
v___y_2855_ = v_a_2832_;
v___y_2856_ = v_a_2833_;
v___y_2857_ = v_a_2834_;
v___y_2858_ = v_a_2835_;
v___y_2859_ = v_a_2836_;
goto v___jp_2848_;
}
v___jp_2848_:
{
lean_object* v___x_2860_; 
v___x_2860_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_2844_, v_info_2825_, v___y_2850_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2866_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1);
v___x_2863_ = l_Lean_indentExpr(v___x_2838_);
lean_inc_ref(v___x_2863_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v___x_2864_);
v___x_2866_ = v___x_2846_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2864_);
v___x_2866_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2861_, v_goal_2824_, v___x_2866_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref_known(v___x_2867_, 1);
if (lean_obj_tag(v_a_2868_) == 1)
{
lean_object* v_mvarIds_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___x_2863_);
v_mvarIds_2869_ = lean_ctor_get(v_a_2868_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2871_ = v_a_2868_;
v_isShared_2872_ = v_isSharedCheck_2895_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_mvarIds_2869_);
lean_dec(v_a_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2895_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2874_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_2869_, v___x_2873_, v___y_2849_, v___y_2850_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
lean_dec(v_mvarIds_2869_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2886_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2877_ = v___x_2874_;
v_isShared_2878_ = v_isSharedCheck_2886_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2874_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2886_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2879_ = lean_array_to_list(v_a_2875_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2879_);
v___x_2881_ = v___x_2871_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2883_; 
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2881_);
v___x_2883_ = v___x_2877_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_del_object(v___x_2871_);
v_a_2887_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2874_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2874_);
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
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec(v_a_2868_);
v___x_2896_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3);
v___x_2897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
lean_ctor_set(v___x_2897_, 1, v___x_2863_);
v___x_2898_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2897_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
return v___x_2898_;
}
}
else
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2906_; 
lean_dec_ref(v___x_2863_);
v_a_2899_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2901_ = v___x_2867_;
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2867_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2906_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v___x_2904_; 
if (v_isShared_2902_ == 0)
{
v___x_2904_ = v___x_2901_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_a_2899_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_del_object(v___x_2846_);
lean_dec_ref(v___x_2838_);
lean_dec(v_goal_2824_);
v_a_2908_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2860_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2860_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
}
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec(v_a_2840_);
lean_dec_ref(v___x_2838_);
lean_dec_ref(v_info_2825_);
lean_dec(v_goal_2824_);
v___x_3009_ = lean_box(0);
if (v_isShared_2843_ == 0)
{
lean_ctor_set(v___x_2842_, 0, v___x_3009_);
v___x_3011_ = v___x_2842_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec_ref(v___x_2838_);
lean_dec_ref(v_info_2825_);
lean_dec(v_goal_2824_);
v_a_3014_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2839_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2839_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3022_, lean_object* v_info_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_3022_, v_info_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
lean_dec(v_a_3034_);
lean_dec_ref(v_a_3033_);
lean_dec(v_a_3032_);
lean_dec_ref(v_a_3031_);
lean_dec(v_a_3030_);
lean_dec_ref(v_a_3029_);
lean_dec(v_a_3028_);
lean_dec_ref(v_a_3027_);
lean_dec(v_a_3026_);
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3037_, lean_object* v_as_x27_3038_, lean_object* v_b_3039_, lean_object* v_a_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3038_, v_b_3039_, v___y_3041_, v___y_3042_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3054_, lean_object* v_as_x27_3055_, lean_object* v_b_3056_, lean_object* v_a_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(v_as_3054_, v_as_x27_3055_, v_b_3056_, v_a_3057_, v___y_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
lean_dec(v___y_3068_);
lean_dec_ref(v___y_3067_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v___y_3058_);
lean_dec(v_as_x27_3055_);
lean_dec(v_as_3054_);
return v_res_3070_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3073_ = l_Lean_stringToMessageData(v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3074_, lean_object* v_info_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_, lean_object* v_a_3079_, lean_object* v_a_3080_, lean_object* v_a_3081_, lean_object* v_a_3082_, lean_object* v_a_3083_, lean_object* v_a_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v___x_3088_; lean_object* v_f_3089_; lean_object* v___x_3090_; 
v___x_3088_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3075_);
v_f_3089_ = l_Lean_Expr_getAppFn(v___x_3088_);
v___x_3090_ = l_Lean_Expr_fvarId_x3f(v_f_3089_);
lean_dec_ref(v_f_3089_);
if (lean_obj_tag(v___x_3090_) == 1)
{
lean_object* v_val_3091_; uint8_t v___x_3092_; lean_object* v___x_3093_; 
v_val_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc_n(v_val_3091_, 2);
lean_dec_ref_known(v___x_3090_, 1);
v___x_3092_ = 0;
v___x_3093_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3091_, v___x_3092_, v_a_3083_, v_a_3085_, v_a_3086_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3181_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3096_ = v___x_3093_;
v_isShared_3097_ = v_isSharedCheck_3181_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3181_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
if (lean_obj_tag(v_a_3094_) == 1)
{
lean_object* v_val_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3176_; 
lean_del_object(v___x_3096_);
v_val_3098_ = lean_ctor_get(v_a_3094_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3100_ = v_a_3094_;
v_isShared_3101_ = v_isSharedCheck_3176_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_val_3098_);
lean_dec(v_a_3094_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3176_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v_options_3148_; uint8_t v_hasTrace_3149_; 
v_options_3148_ = lean_ctor_get(v_a_3085_, 2);
v_hasTrace_3149_ = lean_ctor_get_uint8(v_options_3148_, sizeof(void*)*1);
if (v_hasTrace_3149_ == 0)
{
lean_dec(v_val_3091_);
v___y_3103_ = v_a_3076_;
v___y_3104_ = v_a_3077_;
v___y_3105_ = v_a_3078_;
v___y_3106_ = v_a_3079_;
v___y_3107_ = v_a_3080_;
v___y_3108_ = v_a_3081_;
v___y_3109_ = v_a_3082_;
v___y_3110_ = v_a_3083_;
v___y_3111_ = v_a_3084_;
v___y_3112_ = v_a_3085_;
v___y_3113_ = v_a_3086_;
goto v___jp_3102_;
}
else
{
lean_object* v_inheritedTraceOptions_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_inheritedTraceOptions_3150_ = lean_ctor_get(v_a_3085_, 13);
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3152_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3153_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3150_, v_options_3148_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec(v_val_3091_);
v___y_3103_ = v_a_3076_;
v___y_3104_ = v_a_3077_;
v___y_3105_ = v_a_3078_;
v___y_3106_ = v_a_3079_;
v___y_3107_ = v_a_3080_;
v___y_3108_ = v_a_3081_;
v___y_3109_ = v_a_3082_;
v___y_3110_ = v_a_3083_;
v___y_3111_ = v_a_3084_;
v___y_3112_ = v_a_3085_;
v___y_3113_ = v_a_3086_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3154_; 
v___x_3154_ = l_Lean_FVarId_getUserName___redArg(v_val_3091_, v_a_3083_, v_a_3085_, v_a_3086_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___x_3156_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3157_ = l_Lean_MessageData_ofName(v_a_3155_);
v___x_3158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
v___x_3159_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3151_, v___x_3158_, v_a_3083_, v_a_3084_, v_a_3085_, v_a_3086_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_dec_ref_known(v___x_3159_, 1);
v___y_3103_ = v_a_3076_;
v___y_3104_ = v_a_3077_;
v___y_3105_ = v_a_3078_;
v___y_3106_ = v_a_3079_;
v___y_3107_ = v_a_3080_;
v___y_3108_ = v_a_3081_;
v___y_3109_ = v_a_3082_;
v___y_3110_ = v_a_3083_;
v___y_3111_ = v_a_3084_;
v___y_3112_ = v_a_3085_;
v___y_3113_ = v_a_3086_;
goto v___jp_3102_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_del_object(v___x_3100_);
lean_dec(v_val_3098_);
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_info_3075_);
lean_dec(v_goal_3074_);
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
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
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
lean_del_object(v___x_3100_);
lean_dec(v_val_3098_);
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_info_3075_);
lean_dec(v_goal_3074_);
v_a_3168_ = lean_ctor_get(v___x_3154_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3154_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3154_);
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
v___jp_3102_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3114_ = l_Lean_Expr_getAppNumArgs(v___x_3088_);
v___x_3115_ = lean_mk_empty_array_with_capacity(v___x_3114_);
lean_dec(v___x_3114_);
v___x_3116_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3088_, v___x_3115_);
v___x_3117_ = l_Lean_Expr_betaRev(v_val_3098_, v___x_3116_, v___x_3092_, v___x_3092_);
lean_dec_ref(v___x_3116_);
v___x_3118_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_3117_, v___y_3109_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3120_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v___x_3120_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3074_, v_info_3075_, v_a_3119_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3131_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3123_ = v___x_3120_;
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
else
{
lean_inc(v_a_3121_);
lean_dec(v___x_3120_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3131_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3126_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 0, v_a_3121_);
v___x_3126_ = v___x_3100_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3121_);
v___x_3126_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3128_; 
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3126_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_del_object(v___x_3100_);
v_a_3132_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3120_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3120_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_del_object(v___x_3100_);
lean_dec_ref(v_info_3075_);
lean_dec(v_goal_3074_);
v_a_3140_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3118_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3118_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3179_; 
lean_dec(v_a_3094_);
lean_dec(v_val_3091_);
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_info_3075_);
lean_dec(v_goal_3074_);
v___x_3177_ = lean_box(0);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3177_);
v___x_3179_ = v___x_3096_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
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
lean_dec(v_val_3091_);
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_info_3075_);
lean_dec(v_goal_3074_);
v_a_3182_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3093_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3093_);
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
lean_object* v___x_3190_; lean_object* v___x_3191_; 
lean_dec(v___x_3090_);
lean_dec_ref(v___x_3088_);
lean_dec_ref(v_info_3075_);
lean_dec(v_goal_3074_);
v___x_3190_ = lean_box(0);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3192_, lean_object* v_info_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_3192_, v_info_3193_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_);
lean_dec(v_a_3204_);
lean_dec_ref(v_a_3203_);
lean_dec(v_a_3202_);
lean_dec_ref(v_a_3201_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
lean_dec(v_a_3196_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
return v_res_3206_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0(void){
_start:
{
uint8_t v___x_3207_; uint64_t v___x_3208_; 
v___x_3207_ = 3;
v___x_3208_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3207_);
return v___x_3208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3209_, lean_object* v_info_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v___x_3223_; lean_object* v_a_3225_; lean_object* v_f_3286_; 
v___x_3223_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3210_);
v_f_3286_ = l_Lean_Expr_getAppFn(v___x_3223_);
if (lean_obj_tag(v_f_3286_) == 11)
{
lean_object* v___x_3287_; uint8_t v_foApprox_3288_; uint8_t v_ctxApprox_3289_; uint8_t v_quasiPatternApprox_3290_; uint8_t v_constApprox_3291_; uint8_t v_isDefEqStuckEx_3292_; uint8_t v_unificationHints_3293_; uint8_t v_proofIrrelevance_3294_; uint8_t v_assignSyntheticOpaque_3295_; uint8_t v_offsetCnstrs_3296_; uint8_t v_etaStruct_3297_; uint8_t v_univApprox_3298_; uint8_t v_iota_3299_; uint8_t v_beta_3300_; uint8_t v_proj_3301_; uint8_t v_zeta_3302_; uint8_t v_zetaDelta_3303_; uint8_t v_zetaUnused_3304_; uint8_t v_zetaHave_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3342_; 
v___x_3287_ = l_Lean_Meta_Context_config(v_a_3218_);
v_foApprox_3288_ = lean_ctor_get_uint8(v___x_3287_, 0);
v_ctxApprox_3289_ = lean_ctor_get_uint8(v___x_3287_, 1);
v_quasiPatternApprox_3290_ = lean_ctor_get_uint8(v___x_3287_, 2);
v_constApprox_3291_ = lean_ctor_get_uint8(v___x_3287_, 3);
v_isDefEqStuckEx_3292_ = lean_ctor_get_uint8(v___x_3287_, 4);
v_unificationHints_3293_ = lean_ctor_get_uint8(v___x_3287_, 5);
v_proofIrrelevance_3294_ = lean_ctor_get_uint8(v___x_3287_, 6);
v_assignSyntheticOpaque_3295_ = lean_ctor_get_uint8(v___x_3287_, 7);
v_offsetCnstrs_3296_ = lean_ctor_get_uint8(v___x_3287_, 8);
v_etaStruct_3297_ = lean_ctor_get_uint8(v___x_3287_, 10);
v_univApprox_3298_ = lean_ctor_get_uint8(v___x_3287_, 11);
v_iota_3299_ = lean_ctor_get_uint8(v___x_3287_, 12);
v_beta_3300_ = lean_ctor_get_uint8(v___x_3287_, 13);
v_proj_3301_ = lean_ctor_get_uint8(v___x_3287_, 14);
v_zeta_3302_ = lean_ctor_get_uint8(v___x_3287_, 15);
v_zetaDelta_3303_ = lean_ctor_get_uint8(v___x_3287_, 16);
v_zetaUnused_3304_ = lean_ctor_get_uint8(v___x_3287_, 17);
v_zetaHave_3305_ = lean_ctor_get_uint8(v___x_3287_, 18);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3307_ = v___x_3287_;
v_isShared_3308_ = v_isSharedCheck_3342_;
goto v_resetjp_3306_;
}
else
{
lean_dec(v___x_3287_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3342_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
uint8_t v_trackZetaDelta_3309_; lean_object* v_zetaDeltaSet_3310_; lean_object* v_lctx_3311_; lean_object* v_localInstances_3312_; lean_object* v_defEqCtx_x3f_3313_; lean_object* v_synthPendingDepth_3314_; lean_object* v_canUnfold_x3f_3315_; uint8_t v_univApprox_3316_; uint8_t v_inTypeClassResolution_3317_; uint8_t v_cacheInferType_3318_; uint8_t v___x_3319_; lean_object* v_config_3321_; 
v_trackZetaDelta_3309_ = lean_ctor_get_uint8(v_a_3218_, sizeof(void*)*7);
v_zetaDeltaSet_3310_ = lean_ctor_get(v_a_3218_, 1);
v_lctx_3311_ = lean_ctor_get(v_a_3218_, 2);
v_localInstances_3312_ = lean_ctor_get(v_a_3218_, 3);
v_defEqCtx_x3f_3313_ = lean_ctor_get(v_a_3218_, 4);
v_synthPendingDepth_3314_ = lean_ctor_get(v_a_3218_, 5);
v_canUnfold_x3f_3315_ = lean_ctor_get(v_a_3218_, 6);
v_univApprox_3316_ = lean_ctor_get_uint8(v_a_3218_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3317_ = lean_ctor_get_uint8(v_a_3218_, sizeof(void*)*7 + 2);
v_cacheInferType_3318_ = lean_ctor_get_uint8(v_a_3218_, sizeof(void*)*7 + 3);
v___x_3319_ = 3;
if (v_isShared_3308_ == 0)
{
v_config_3321_ = v___x_3307_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 0, v_foApprox_3288_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 1, v_ctxApprox_3289_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 2, v_quasiPatternApprox_3290_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 3, v_constApprox_3291_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 4, v_isDefEqStuckEx_3292_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 5, v_unificationHints_3293_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 6, v_proofIrrelevance_3294_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 7, v_assignSyntheticOpaque_3295_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 8, v_offsetCnstrs_3296_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 10, v_etaStruct_3297_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 11, v_univApprox_3298_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 12, v_iota_3299_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 13, v_beta_3300_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 14, v_proj_3301_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 15, v_zeta_3302_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 16, v_zetaDelta_3303_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 17, v_zetaUnused_3304_);
lean_ctor_set_uint8(v_reuseFailAlloc_3341_, 18, v_zetaHave_3305_);
v_config_3321_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
uint64_t v___x_3322_; uint64_t v___x_3323_; uint64_t v___x_3324_; uint64_t v___x_3325_; uint64_t v___x_3326_; uint64_t v_key_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
lean_ctor_set_uint8(v_config_3321_, 9, v___x_3319_);
v___x_3322_ = l_Lean_Meta_Context_configKey(v_a_3218_);
v___x_3323_ = 3ULL;
v___x_3324_ = lean_uint64_shift_right(v___x_3322_, v___x_3323_);
v___x_3325_ = lean_uint64_shift_left(v___x_3324_, v___x_3323_);
v___x_3326_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0);
v_key_3327_ = lean_uint64_lor(v___x_3325_, v___x_3326_);
v___x_3328_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3328_, 0, v_config_3321_);
lean_ctor_set_uint64(v___x_3328_, sizeof(void*)*1, v_key_3327_);
lean_inc(v_canUnfold_x3f_3315_);
lean_inc(v_synthPendingDepth_3314_);
lean_inc(v_defEqCtx_x3f_3313_);
lean_inc_ref(v_localInstances_3312_);
lean_inc_ref(v_lctx_3311_);
lean_inc(v_zetaDeltaSet_3310_);
v___x_3329_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v_zetaDeltaSet_3310_);
lean_ctor_set(v___x_3329_, 2, v_lctx_3311_);
lean_ctor_set(v___x_3329_, 3, v_localInstances_3312_);
lean_ctor_set(v___x_3329_, 4, v_defEqCtx_x3f_3313_);
lean_ctor_set(v___x_3329_, 5, v_synthPendingDepth_3314_);
lean_ctor_set(v___x_3329_, 6, v_canUnfold_x3f_3315_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7, v_trackZetaDelta_3309_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7 + 1, v_univApprox_3316_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3317_);
lean_ctor_set_uint8(v___x_3329_, sizeof(void*)*7 + 3, v_cacheInferType_3318_);
v___x_3330_ = l_Lean_Meta_reduceProj_x3f(v_f_3286_, v___x_3329_, v_a_3219_, v_a_3220_, v_a_3221_);
lean_dec_ref_known(v___x_3329_, 7);
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3331_; 
v_a_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3331_);
lean_dec_ref_known(v___x_3330_, 1);
v_a_3225_ = v_a_3331_;
goto v___jp_3224_;
}
else
{
if (lean_obj_tag(v___x_3330_) == 0)
{
lean_object* v_a_3332_; 
v_a_3332_ = lean_ctor_get(v___x_3330_, 0);
lean_inc(v_a_3332_);
lean_dec_ref_known(v___x_3330_, 1);
v_a_3225_ = v_a_3332_;
goto v___jp_3224_;
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v___x_3223_);
lean_dec_ref(v_info_3210_);
lean_dec(v_goal_3209_);
v_a_3333_ = lean_ctor_get(v___x_3330_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3330_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3330_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3330_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref(v_f_3286_);
lean_dec_ref(v___x_3223_);
lean_dec_ref(v_info_3210_);
lean_dec(v_goal_3209_);
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
return v___x_3344_;
}
v___jp_3224_:
{
if (lean_obj_tag(v_a_3225_) == 1)
{
lean_object* v_val_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3283_; 
v_val_3226_ = lean_ctor_get(v_a_3225_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_a_3225_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3228_ = v_a_3225_;
v_isShared_3229_ = v_isSharedCheck_3283_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_val_3226_);
lean_dec(v_a_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3283_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3226_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3231_, v_a_3217_);
if (lean_obj_tag(v___x_3232_) == 0)
{
lean_object* v_a_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v_a_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_a_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_Lean_Expr_getAppNumArgs(v___x_3223_);
v___x_3235_ = lean_mk_empty_array_with_capacity(v___x_3234_);
lean_dec(v___x_3234_);
v___x_3236_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3223_, v___x_3235_);
v___x_3237_ = l_Lean_Meta_Sym_betaRevS___redArg(v_a_3233_, v___x_3236_, v_a_3217_);
lean_dec_ref(v___x_3236_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3239_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3209_, v_info_3210_, v_a_3238_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3250_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3250_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3250_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_a_3240_);
v___x_3245_ = v___x_3228_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3245_);
v___x_3247_ = v___x_3242_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_del_object(v___x_3228_);
v_a_3251_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3239_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3239_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_del_object(v___x_3228_);
lean_dec_ref(v_info_3210_);
lean_dec(v_goal_3209_);
v_a_3259_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3237_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3237_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v_a_3267_; lean_object* v___x_3269_; uint8_t v_isShared_3270_; uint8_t v_isSharedCheck_3274_; 
lean_del_object(v___x_3228_);
lean_dec_ref(v___x_3223_);
lean_dec_ref(v_info_3210_);
lean_dec(v_goal_3209_);
v_a_3267_ = lean_ctor_get(v___x_3232_, 0);
v_isSharedCheck_3274_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3269_ = v___x_3232_;
v_isShared_3270_ = v_isSharedCheck_3274_;
goto v_resetjp_3268_;
}
else
{
lean_inc(v_a_3267_);
lean_dec(v___x_3232_);
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
lean_del_object(v___x_3228_);
lean_dec_ref(v___x_3223_);
lean_dec_ref(v_info_3210_);
lean_dec(v_goal_3209_);
v_a_3275_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3230_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3230_);
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
lean_object* v___x_3284_; lean_object* v___x_3285_; 
lean_dec(v_a_3225_);
lean_dec_ref(v___x_3223_);
lean_dec_ref(v_info_3210_);
lean_dec(v_goal_3209_);
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
return v___x_3285_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_3345_, lean_object* v_info_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_3345_, v_info_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec(v_a_3348_);
lean_dec_ref(v_a_3347_);
return v_res_3359_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_3362_ = l_Lean_stringToMessageData(v___x_3361_);
return v___x_3362_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_3365_ = l_Lean_stringToMessageData(v___x_3364_);
return v___x_3365_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_3368_ = l_Lean_stringToMessageData(v___x_3367_);
return v___x_3368_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_3371_ = l_Lean_stringToMessageData(v___x_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
if (lean_obj_tag(v_a_3372_) == 0)
{
lean_object* v___x_3374_; 
v___x_3374_ = l_List_reverse___redArg(v_a_3373_);
return v___x_3374_;
}
else
{
lean_object* v_head_3375_; lean_object* v_tail_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3404_; 
v_head_3375_ = lean_ctor_get(v_a_3372_, 0);
v_tail_3376_ = lean_ctor_get(v_a_3372_, 1);
v_isSharedCheck_3404_ = !lean_is_exclusive(v_a_3372_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3378_ = v_a_3372_;
v_isShared_3379_ = v_isSharedCheck_3404_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_tail_3376_);
lean_inc(v_head_3375_);
lean_dec(v_a_3372_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3404_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___y_3381_; 
switch(lean_obj_tag(v_head_3375_))
{
case 0:
{
lean_object* v_declName_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_declName_3386_ = lean_ctor_get(v_head_3375_, 0);
lean_inc(v_declName_3386_);
lean_dec_ref_known(v_head_3375_, 1);
v___x_3387_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3388_ = l_Lean_MessageData_ofName(v_declName_3386_);
v___x_3389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___y_3381_ = v___x_3389_;
goto v___jp_3380_;
}
case 1:
{
lean_object* v_fvarId_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; 
v_fvarId_3390_ = lean_ctor_get(v_head_3375_, 0);
lean_inc(v_fvarId_3390_);
lean_dec_ref_known(v_head_3375_, 1);
v___x_3391_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3392_ = l_Lean_mkFVar(v_fvarId_3390_);
v___x_3393_ = l_Lean_MessageData_ofExpr(v___x_3392_);
v___x_3394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3391_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___y_3381_ = v___x_3394_;
goto v___jp_3380_;
}
default: 
{
lean_object* v_ref_3395_; lean_object* v_proof_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; 
v_ref_3395_ = lean_ctor_get(v_head_3375_, 1);
lean_inc(v_ref_3395_);
v_proof_3396_ = lean_ctor_get(v_head_3375_, 2);
lean_inc_ref(v_proof_3396_);
lean_dec_ref_known(v_head_3375_, 3);
v___x_3397_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3398_ = l_Lean_MessageData_ofSyntax(v_ref_3395_);
v___x_3399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = l_Lean_MessageData_ofExpr(v_proof_3396_);
v___x_3403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___y_3381_ = v___x_3403_;
goto v___jp_3380_;
}
}
v___jp_3380_:
{
lean_object* v___x_3383_; 
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 1, v_a_3373_);
lean_ctor_set(v___x_3378_, 0, v___y_3381_);
v___x_3383_ = v___x_3378_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___y_3381_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_a_3373_);
v___x_3383_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
v_a_3372_ = v_tail_3376_;
v_a_3373_ = v___x_3383_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_3405_, size_t v_i_3406_, lean_object* v_bs_3407_){
_start:
{
uint8_t v___x_3408_; 
v___x_3408_ = lean_usize_dec_lt(v_i_3406_, v_sz_3405_);
if (v___x_3408_ == 0)
{
return v_bs_3407_;
}
else
{
lean_object* v_v_3409_; lean_object* v_proof_3410_; lean_object* v___x_3411_; lean_object* v_bs_x27_3412_; size_t v___x_3413_; size_t v___x_3414_; lean_object* v___x_3415_; 
v_v_3409_ = lean_array_uget_borrowed(v_bs_3407_, v_i_3406_);
v_proof_3410_ = lean_ctor_get(v_v_3409_, 1);
lean_inc_ref(v_proof_3410_);
v___x_3411_ = lean_unsigned_to_nat(0u);
v_bs_x27_3412_ = lean_array_uset(v_bs_3407_, v_i_3406_, v___x_3411_);
v___x_3413_ = ((size_t)1ULL);
v___x_3414_ = lean_usize_add(v_i_3406_, v___x_3413_);
v___x_3415_ = lean_array_uset(v_bs_x27_3412_, v_i_3406_, v_proof_3410_);
v_i_3406_ = v___x_3414_;
v_bs_3407_ = v___x_3415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_3417_, lean_object* v_i_3418_, lean_object* v_bs_3419_){
_start:
{
size_t v_sz_boxed_3420_; size_t v_i_boxed_3421_; lean_object* v_res_3422_; 
v_sz_boxed_3420_ = lean_unbox_usize(v_sz_3417_);
lean_dec(v_sz_3417_);
v_i_boxed_3421_ = lean_unbox_usize(v_i_3418_);
lean_dec(v_i_3418_);
v_res_3422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_3420_, v_i_boxed_3421_, v_bs_3419_);
return v_res_3422_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_3425_ = l_Lean_stringToMessageData(v___x_3424_);
return v___x_3425_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_3438_, lean_object* v_monad_3439_, lean_object* v_thms_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_){
_start:
{
uint8_t v_errorOnMissingSpec_3447_; 
v_errorOnMissingSpec_3447_ = lean_ctor_get_uint8(v_a_3441_, sizeof(void*)*4 + 2);
if (v_errorOnMissingSpec_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3448_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_3448_, 0, v_prog_3438_);
lean_ctor_set(v___x_3448_, 1, v_monad_3439_);
lean_ctor_set(v___x_3448_, 2, v_thms_3440_);
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
v___x_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3449_);
return v___x_3450_;
}
else
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = lean_array_get_size(v_thms_3440_);
v___x_3452_ = lean_unsigned_to_nat(0u);
v___x_3453_ = lean_nat_dec_eq(v___x_3451_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; size_t v_sz_3463_; size_t v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3454_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_3455_ = l_Lean_MessageData_ofExpr(v_monad_3439_);
v___x_3456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_3458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = l_Lean_MessageData_ofExpr(v_prog_3438_);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_3462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v_sz_3463_ = lean_array_size(v_thms_3440_);
v___x_3464_ = ((size_t)0ULL);
v___x_3465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_3463_, v___x_3464_, v_thms_3440_);
v___x_3466_ = lean_array_to_list(v___x_3465_);
v___x_3467_ = lean_box(0);
v___x_3468_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_3466_, v___x_3467_);
v___x_3469_ = l_Lean_MessageData_ofList(v___x_3468_);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3462_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
v___x_3471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3472_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
return v___x_3473_;
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_dec_ref(v_thms_3440_);
lean_dec_ref(v_monad_3439_);
v___x_3474_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_3475_ = l_Lean_MessageData_ofExpr(v_prog_3438_);
v___x_3476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3474_);
lean_ctor_set(v___x_3476_, 1, v___x_3475_);
v___x_3477_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3478_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_);
return v___x_3479_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_3480_, lean_object* v_monad_3481_, lean_object* v_thms_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3480_, v_monad_3481_, v_thms_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec_ref(v_a_3483_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_3490_, lean_object* v_monad_3491_, lean_object* v_thms_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v___x_3505_; 
v___x_3505_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3490_, v_monad_3491_, v_thms_3492_, v_a_3493_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_);
return v___x_3505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_3506_, lean_object* v_monad_3507_, lean_object* v_thms_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_){
_start:
{
lean_object* v_res_3521_; 
v_res_3521_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(v_prog_3506_, v_monad_3507_, v_thms_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec_ref(v_a_3512_);
lean_dec(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
if (lean_obj_tag(v_a_3522_) == 0)
{
lean_object* v___x_3524_; 
v___x_3524_ = l_List_reverse___redArg(v_a_3523_);
return v___x_3524_;
}
else
{
lean_object* v_head_3525_; lean_object* v_tail_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3535_; 
v_head_3525_ = lean_ctor_get(v_a_3522_, 0);
v_tail_3526_ = lean_ctor_get(v_a_3522_, 1);
v_isSharedCheck_3535_ = !lean_is_exclusive(v_a_3522_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3528_ = v_a_3522_;
v_isShared_3529_ = v_isSharedCheck_3535_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_tail_3526_);
lean_inc(v_head_3525_);
lean_dec(v_a_3522_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3535_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = l_Lean_MessageData_ofExpr(v_head_3525_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v_a_3523_);
lean_ctor_set(v___x_3528_, 0, v___x_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3530_);
lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_a_3523_);
v___x_3532_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
v_a_3522_ = v_tail_3526_;
v_a_3523_ = v___x_3532_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_3538_ = l_Lean_stringToMessageData(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_3541_ = l_Lean_stringToMessageData(v___x_3540_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_3544_ = l_Lean_stringToMessageData(v___x_3543_);
return v___x_3544_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
return v___x_3550_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
return v___x_3553_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_3556_ = l_Lean_stringToMessageData(v___x_3555_);
return v___x_3556_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_3559_ = l_Lean_stringToMessageData(v___x_3558_);
return v___x_3559_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_3562_ = l_Lean_stringToMessageData(v___x_3561_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_3568_ = l_Lean_stringToMessageData(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23(void){
_start:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22));
v___x_3571_ = l_Lean_stringToMessageData(v___x_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3573_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24));
v___x_3574_ = l_Lean_stringToMessageData(v___x_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_scope_3575_, lean_object* v_goal_3576_, lean_object* v_info_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3627_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3631_; lean_object* v___y_3632_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3728_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; uint8_t v___y_3790_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v_options_3840_; lean_object* v_inheritedTraceOptions_3841_; uint8_t v_hasTrace_3842_; lean_object* v_cls_3843_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; 
v_options_3840_ = lean_ctor_get(v_a_3587_, 2);
v_inheritedTraceOptions_3841_ = lean_ctor_get(v_a_3587_, 13);
v_hasTrace_3842_ = lean_ctor_get_uint8(v_options_3840_, sizeof(void*)*1);
v_cls_3843_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_3842_ == 0)
{
v___y_3872_ = v_a_3578_;
v___y_3873_ = v_a_3579_;
v___y_3874_ = v_a_3580_;
v___y_3875_ = v_a_3581_;
v___y_3876_ = v_a_3582_;
v___y_3877_ = v_a_3583_;
v___y_3878_ = v_a_3584_;
v___y_3879_ = v_a_3585_;
v___y_3880_ = v_a_3586_;
v___y_3881_ = v_a_3587_;
v___y_3882_ = v_a_3588_;
goto v___jp_3871_;
}
else
{
lean_object* v___x_3947_; uint8_t v___x_3948_; 
v___x_3947_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3948_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3841_, v_options_3840_, v___x_3947_);
if (v___x_3948_ == 0)
{
v___y_3872_ = v_a_3578_;
v___y_3873_ = v_a_3579_;
v___y_3874_ = v_a_3580_;
v___y_3875_ = v_a_3581_;
v___y_3876_ = v_a_3582_;
v___y_3877_ = v_a_3583_;
v___y_3878_ = v_a_3584_;
v___y_3879_ = v_a_3585_;
v___y_3880_ = v_a_3586_;
v___y_3881_ = v_a_3587_;
v___y_3882_ = v_a_3588_;
goto v___jp_3871_;
}
else
{
lean_object* v_excessArgs_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
v_excessArgs_3949_ = lean_ctor_get(v_info_3577_, 2);
v___x_3950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23);
v___x_3951_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3577_);
v___x_3952_ = l_Lean_MessageData_ofExpr(v___x_3951_);
v___x_3953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3950_);
lean_ctor_set(v___x_3953_, 1, v___x_3952_);
v___x_3954_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
lean_inc_ref(v_excessArgs_3949_);
v___x_3956_ = lean_array_to_list(v_excessArgs_3949_);
v___x_3957_ = lean_box(0);
v___x_3958_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3956_, v___x_3957_);
v___x_3959_ = l_Lean_MessageData_ofList(v___x_3958_);
v___x_3960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3955_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3843_, v___x_3960_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_dec_ref_known(v___x_3961_, 1);
v___y_3872_ = v_a_3578_;
v___y_3873_ = v_a_3579_;
v___y_3874_ = v_a_3580_;
v___y_3875_ = v_a_3581_;
v___y_3876_ = v_a_3582_;
v___y_3877_ = v_a_3583_;
v___y_3878_ = v_a_3584_;
v___y_3879_ = v_a_3585_;
v___y_3880_ = v_a_3586_;
v___y_3881_ = v_a_3587_;
v___y_3882_ = v_a_3588_;
goto v___jp_3871_;
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
lean_dec_ref(v_scope_3575_);
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3961_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3961_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
}
v___jp_3590_:
{
lean_object* v_excessArgs_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_excessArgs_3600_ = lean_ctor_get(v_info_3577_, 2);
lean_inc_ref(v_excessArgs_3600_);
lean_inc_ref(v___y_3593_);
v___x_3601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___y_3593_);
lean_ctor_set(v___x_3601_, 1, v___y_3599_);
v___x_3602_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3601_);
lean_ctor_set(v___x_3603_, 1, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v___y_3595_);
v___x_3605_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l_Lean_indentExpr(v___y_3594_);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_3577_);
lean_dec_ref(v_info_3577_);
v___x_3612_ = l_Lean_indentExpr(v___x_3611_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3610_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_array_to_list(v_excessArgs_3600_);
v___x_3617_ = lean_box(0);
v___x_3618_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3616_, v___x_3617_);
v___x_3619_ = l_Lean_MessageData_ofList(v___x_3618_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3615_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = l_Lean_indentExpr(v___y_3591_);
v___x_3624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3622_);
lean_ctor_set(v___x_3624_, 1, v___x_3623_);
v___x_3625_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3624_, v___y_3592_, v___y_3598_, v___y_3597_, v___y_3596_);
return v___x_3625_;
}
v___jp_3626_:
{
if (lean_obj_tag(v___y_3641_) == 0)
{
lean_object* v_a_3642_; 
v_a_3642_ = lean_ctor_get(v___y_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___y_3641_, 1);
if (lean_obj_tag(v_a_3642_) == 1)
{
lean_object* v_val_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3713_; 
v_val_3643_ = lean_ctor_get(v_a_3642_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v_a_3642_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3645_ = v_a_3642_;
v_isShared_3646_ = v_isSharedCheck_3713_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_val_3643_);
lean_dec(v_a_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3713_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3651_; 
v___x_3647_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
v___x_3648_ = l_Lean_indentExpr(v___y_3640_);
lean_inc_ref(v___x_3648_);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3649_);
v___x_3651_ = v___x_3645_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3649_);
v___x_3651_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
lean_object* v___x_3652_; 
lean_inc(v_goal_3576_);
lean_inc(v_val_3643_);
v___x_3652_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_3643_, v_goal_3576_, v___x_3651_, v___y_3638_, v___y_3634_, v___y_3631_, v___y_3637_, v___y_3632_, v___y_3633_, v___y_3629_, v___y_3630_, v___y_3639_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3703_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3703_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3703_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
if (lean_obj_tag(v_a_3653_) == 1)
{
lean_object* v_mvarIds_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
lean_dec_ref(v___x_3648_);
lean_dec(v_val_3643_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_mvarIds_3657_ = lean_ctor_get(v_a_3653_, 0);
lean_inc(v_mvarIds_3657_);
lean_dec_ref_known(v_a_3653_, 1);
v___x_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___y_3627_);
lean_ctor_set(v___x_3658_, 1, v_mvarIds_3657_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3658_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
return v___x_3660_;
}
}
else
{
lean_object* v_expr_3662_; lean_object* v___x_3663_; 
lean_del_object(v___x_3655_);
lean_dec(v_a_3653_);
lean_dec_ref(v___y_3627_);
v_expr_3662_ = lean_ctor_get(v_val_3643_, 0);
lean_inc_ref(v_expr_3662_);
lean_dec(v_val_3643_);
lean_inc(v___y_3636_);
lean_inc_ref(v___y_3635_);
lean_inc(v___y_3639_);
lean_inc_ref(v___y_3630_);
v___x_3663_ = lean_infer_type(v_expr_3662_, v___y_3630_, v___y_3639_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v___x_3665_ = l_Lean_MVarId_getType(v_goal_3576_, v___y_3630_, v___y_3639_, v___y_3635_, v___y_3636_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v_proof_3667_; lean_object* v___x_3668_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v_proof_3667_ = lean_ctor_get(v___y_3628_, 1);
lean_inc_ref(v_proof_3667_);
lean_dec_ref(v___y_3628_);
v___x_3668_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
switch(lean_obj_tag(v_proof_3667_))
{
case 0:
{
lean_object* v_declName_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v_declName_3669_ = lean_ctor_get(v_proof_3667_, 0);
lean_inc(v_declName_3669_);
lean_dec_ref_known(v_proof_3667_, 1);
v___x_3670_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3671_ = l_Lean_MessageData_ofName(v_declName_3669_);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___y_3591_ = v_a_3664_;
v___y_3592_ = v___y_3630_;
v___y_3593_ = v___x_3668_;
v___y_3594_ = v_a_3666_;
v___y_3595_ = v___x_3648_;
v___y_3596_ = v___y_3636_;
v___y_3597_ = v___y_3635_;
v___y_3598_ = v___y_3639_;
v___y_3599_ = v___x_3672_;
goto v___jp_3590_;
}
case 1:
{
lean_object* v_fvarId_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v_fvarId_3673_ = lean_ctor_get(v_proof_3667_, 0);
lean_inc(v_fvarId_3673_);
lean_dec_ref_known(v_proof_3667_, 1);
v___x_3674_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3675_ = l_Lean_mkFVar(v_fvarId_3673_);
v___x_3676_ = l_Lean_MessageData_ofExpr(v___x_3675_);
v___x_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3674_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___y_3591_ = v_a_3664_;
v___y_3592_ = v___y_3630_;
v___y_3593_ = v___x_3668_;
v___y_3594_ = v_a_3666_;
v___y_3595_ = v___x_3648_;
v___y_3596_ = v___y_3636_;
v___y_3597_ = v___y_3635_;
v___y_3598_ = v___y_3639_;
v___y_3599_ = v___x_3677_;
goto v___jp_3590_;
}
default: 
{
lean_object* v_ref_3678_; lean_object* v_proof_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_ref_3678_ = lean_ctor_get(v_proof_3667_, 1);
lean_inc(v_ref_3678_);
v_proof_3679_ = lean_ctor_get(v_proof_3667_, 2);
lean_inc_ref(v_proof_3679_);
lean_dec_ref_known(v_proof_3667_, 3);
v___x_3680_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3681_ = l_Lean_MessageData_ofSyntax(v_ref_3678_);
v___x_3682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3680_);
lean_ctor_set(v___x_3682_, 1, v___x_3681_);
v___x_3683_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3682_);
lean_ctor_set(v___x_3684_, 1, v___x_3683_);
v___x_3685_ = l_Lean_MessageData_ofExpr(v_proof_3679_);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___y_3591_ = v_a_3664_;
v___y_3592_ = v___y_3630_;
v___y_3593_ = v___x_3668_;
v___y_3594_ = v_a_3666_;
v___y_3595_ = v___x_3648_;
v___y_3596_ = v___y_3636_;
v___y_3597_ = v___y_3635_;
v___y_3598_ = v___y_3639_;
v___y_3599_ = v___x_3686_;
goto v___jp_3590_;
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_dec(v_a_3664_);
lean_dec_ref(v___x_3648_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v_info_3577_);
v_a_3687_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3665_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3665_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec_ref(v___x_3648_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_a_3695_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3663_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3663_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec_ref(v___x_3648_);
lean_dec(v_val_3643_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_a_3704_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3652_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3652_);
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
}
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
lean_dec(v_a_3642_);
lean_dec_ref(v___y_3627_);
lean_dec(v_goal_3576_);
v___x_3714_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_3577_);
lean_dec_ref(v_info_3577_);
v___x_3715_ = lean_unsigned_to_nat(1u);
v___x_3716_ = lean_mk_empty_array_with_capacity(v___x_3715_);
v___x_3717_ = lean_array_push(v___x_3716_, v___y_3628_);
v___x_3718_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___y_3640_, v___x_3714_, v___x_3717_, v___y_3638_, v___y_3630_, v___y_3639_, v___y_3635_, v___y_3636_);
return v___x_3718_;
}
}
else
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3726_; 
lean_dec_ref(v___y_3640_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v___y_3627_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_a_3719_ = lean_ctor_get(v___y_3641_, 0);
v_isSharedCheck_3726_ = !lean_is_exclusive(v___y_3641_);
if (v_isSharedCheck_3726_ == 0)
{
v___x_3721_ = v___y_3641_;
v_isShared_3722_ = v_isSharedCheck_3726_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___y_3641_);
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
v___jp_3727_:
{
lean_object* v_excessArgs_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_excessArgs_3746_ = lean_ctor_get(v_info_3577_, 2);
lean_inc_ref(v___y_3741_);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___y_3741_);
lean_ctor_set(v___x_3747_, 1, v___y_3745_);
v___x_3748_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
lean_inc_ref(v___y_3744_);
v___x_3750_ = l_Lean_indentExpr(v___y_3744_);
v___x_3751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3749_);
lean_ctor_set(v___x_3751_, 1, v___x_3750_);
v___x_3752_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
v___x_3753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3751_);
lean_ctor_set(v___x_3753_, 1, v___x_3752_);
v___x_3754_ = l_Lean_Exception_toMessageData(v___y_3731_);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = l_Lean_indentExpr(v___y_3735_);
v___x_3759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3757_);
lean_ctor_set(v___x_3759_, 1, v___x_3758_);
v___x_3760_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_3577_);
v___x_3763_ = l_Lean_indentExpr(v___x_3762_);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3761_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___x_3765_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
lean_inc_ref(v_excessArgs_3746_);
v___x_3767_ = lean_array_to_list(v_excessArgs_3746_);
v___x_3768_ = lean_box(0);
v___x_3769_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3767_, v___x_3768_);
v___x_3770_ = l_Lean_MessageData_ofList(v___x_3769_);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3766_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3771_, v___y_3732_, v___y_3743_, v___y_3738_, v___y_3739_);
v___y_3627_ = v___y_3728_;
v___y_3628_ = v___y_3729_;
v___y_3629_ = v___y_3730_;
v___y_3630_ = v___y_3732_;
v___y_3631_ = v___y_3734_;
v___y_3632_ = v___y_3733_;
v___y_3633_ = v___y_3736_;
v___y_3634_ = v___y_3737_;
v___y_3635_ = v___y_3738_;
v___y_3636_ = v___y_3739_;
v___y_3637_ = v___y_3740_;
v___y_3638_ = v___y_3742_;
v___y_3639_ = v___y_3743_;
v___y_3640_ = v___y_3744_;
v___y_3641_ = v___x_3772_;
goto v___jp_3626_;
}
v___jp_3773_:
{
if (v___y_3790_ == 0)
{
lean_object* v___x_3791_; 
lean_dec_ref(v___y_3777_);
lean_inc(v_goal_3576_);
v___x_3791_ = l_Lean_MVarId_getType(v_goal_3576_, v___y_3779_, v___y_3788_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v_proof_3793_; lean_object* v___x_3794_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v_proof_3793_ = lean_ctor_get(v___y_3775_, 1);
v___x_3794_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
switch(lean_obj_tag(v_proof_3793_))
{
case 0:
{
lean_object* v_declName_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_declName_3795_ = lean_ctor_get(v_proof_3793_, 0);
v___x_3796_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3795_);
v___x_3797_ = l_Lean_MessageData_ofName(v_declName_3795_);
v___x_3798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3798_, 0, v___x_3796_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
v___y_3728_ = v___y_3774_;
v___y_3729_ = v___y_3775_;
v___y_3730_ = v___y_3776_;
v___y_3731_ = v___y_3778_;
v___y_3732_ = v___y_3779_;
v___y_3733_ = v___y_3780_;
v___y_3734_ = v___y_3781_;
v___y_3735_ = v_a_3792_;
v___y_3736_ = v___y_3782_;
v___y_3737_ = v___y_3783_;
v___y_3738_ = v___y_3784_;
v___y_3739_ = v___y_3785_;
v___y_3740_ = v___y_3786_;
v___y_3741_ = v___x_3794_;
v___y_3742_ = v___y_3787_;
v___y_3743_ = v___y_3788_;
v___y_3744_ = v___y_3789_;
v___y_3745_ = v___x_3798_;
goto v___jp_3727_;
}
case 1:
{
lean_object* v_fvarId_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v_fvarId_3799_ = lean_ctor_get(v_proof_3793_, 0);
v___x_3800_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3799_);
v___x_3801_ = l_Lean_mkFVar(v_fvarId_3799_);
v___x_3802_ = l_Lean_MessageData_ofExpr(v___x_3801_);
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3800_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___y_3728_ = v___y_3774_;
v___y_3729_ = v___y_3775_;
v___y_3730_ = v___y_3776_;
v___y_3731_ = v___y_3778_;
v___y_3732_ = v___y_3779_;
v___y_3733_ = v___y_3780_;
v___y_3734_ = v___y_3781_;
v___y_3735_ = v_a_3792_;
v___y_3736_ = v___y_3782_;
v___y_3737_ = v___y_3783_;
v___y_3738_ = v___y_3784_;
v___y_3739_ = v___y_3785_;
v___y_3740_ = v___y_3786_;
v___y_3741_ = v___x_3794_;
v___y_3742_ = v___y_3787_;
v___y_3743_ = v___y_3788_;
v___y_3744_ = v___y_3789_;
v___y_3745_ = v___x_3803_;
goto v___jp_3727_;
}
default: 
{
lean_object* v_ref_3804_; lean_object* v_proof_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_ref_3804_ = lean_ctor_get(v_proof_3793_, 1);
v_proof_3805_ = lean_ctor_get(v_proof_3793_, 2);
v___x_3806_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3804_);
v___x_3807_ = l_Lean_MessageData_ofSyntax(v_ref_3804_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
lean_inc_ref(v_proof_3805_);
v___x_3811_ = l_Lean_MessageData_ofExpr(v_proof_3805_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___y_3728_ = v___y_3774_;
v___y_3729_ = v___y_3775_;
v___y_3730_ = v___y_3776_;
v___y_3731_ = v___y_3778_;
v___y_3732_ = v___y_3779_;
v___y_3733_ = v___y_3780_;
v___y_3734_ = v___y_3781_;
v___y_3735_ = v_a_3792_;
v___y_3736_ = v___y_3782_;
v___y_3737_ = v___y_3783_;
v___y_3738_ = v___y_3784_;
v___y_3739_ = v___y_3785_;
v___y_3740_ = v___y_3786_;
v___y_3741_ = v___x_3794_;
v___y_3742_ = v___y_3787_;
v___y_3743_ = v___y_3788_;
v___y_3744_ = v___y_3789_;
v___y_3745_ = v___x_3812_;
goto v___jp_3727_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_a_3813_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3791_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3791_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_dec_ref(v___y_3778_);
v___y_3627_ = v___y_3774_;
v___y_3628_ = v___y_3775_;
v___y_3629_ = v___y_3776_;
v___y_3630_ = v___y_3779_;
v___y_3631_ = v___y_3781_;
v___y_3632_ = v___y_3780_;
v___y_3633_ = v___y_3782_;
v___y_3634_ = v___y_3783_;
v___y_3635_ = v___y_3784_;
v___y_3636_ = v___y_3785_;
v___y_3637_ = v___y_3786_;
v___y_3638_ = v___y_3787_;
v___y_3639_ = v___y_3788_;
v___y_3640_ = v___y_3789_;
v___y_3641_ = v___y_3777_;
goto v___jp_3626_;
}
}
v___jp_3821_:
{
lean_object* v___x_3836_; 
lean_inc_ref(v_info_3577_);
lean_inc_ref(v___y_3823_);
v___x_3836_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v___y_3823_, v_info_3577_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_3836_) == 0)
{
v___y_3627_ = v___y_3822_;
v___y_3628_ = v___y_3823_;
v___y_3629_ = v___y_3831_;
v___y_3630_ = v___y_3832_;
v___y_3631_ = v___y_3827_;
v___y_3632_ = v___y_3829_;
v___y_3633_ = v___y_3830_;
v___y_3634_ = v___y_3826_;
v___y_3635_ = v___y_3834_;
v___y_3636_ = v___y_3835_;
v___y_3637_ = v___y_3828_;
v___y_3638_ = v___y_3825_;
v___y_3639_ = v___y_3833_;
v___y_3640_ = v___y_3824_;
v___y_3641_ = v___x_3836_;
goto v___jp_3626_;
}
else
{
lean_object* v_a_3837_; uint8_t v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
v___x_3838_ = l_Lean_Exception_isInterrupt(v_a_3837_);
if (v___x_3838_ == 0)
{
uint8_t v___x_3839_; 
lean_inc(v_a_3837_);
v___x_3839_ = l_Lean_Exception_isRuntime(v_a_3837_);
v___y_3774_ = v___y_3822_;
v___y_3775_ = v___y_3823_;
v___y_3776_ = v___y_3831_;
v___y_3777_ = v___x_3836_;
v___y_3778_ = v_a_3837_;
v___y_3779_ = v___y_3832_;
v___y_3780_ = v___y_3829_;
v___y_3781_ = v___y_3827_;
v___y_3782_ = v___y_3830_;
v___y_3783_ = v___y_3826_;
v___y_3784_ = v___y_3834_;
v___y_3785_ = v___y_3835_;
v___y_3786_ = v___y_3828_;
v___y_3787_ = v___y_3825_;
v___y_3788_ = v___y_3833_;
v___y_3789_ = v___y_3824_;
v___y_3790_ = v___x_3839_;
goto v___jp_3773_;
}
else
{
v___y_3774_ = v___y_3822_;
v___y_3775_ = v___y_3823_;
v___y_3776_ = v___y_3831_;
v___y_3777_ = v___x_3836_;
v___y_3778_ = v_a_3837_;
v___y_3779_ = v___y_3832_;
v___y_3780_ = v___y_3829_;
v___y_3781_ = v___y_3827_;
v___y_3782_ = v___y_3830_;
v___y_3783_ = v___y_3826_;
v___y_3784_ = v___y_3834_;
v___y_3785_ = v___y_3835_;
v___y_3786_ = v___y_3828_;
v___y_3787_ = v___y_3825_;
v___y_3788_ = v___y_3833_;
v___y_3789_ = v___y_3824_;
v___y_3790_ = v___x_3838_;
goto v___jp_3773_;
}
}
}
v___jp_3844_:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___y_3848_);
lean_ctor_set(v___x_3861_, 1, v___y_3860_);
v___x_3862_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3843_, v___x_3861_, v___y_3856_, v___y_3849_, v___y_3850_, v___y_3858_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_dec_ref_known(v___x_3862_, 1);
v___y_3822_ = v___y_3845_;
v___y_3823_ = v___y_3847_;
v___y_3824_ = v___y_3859_;
v___y_3825_ = v___y_3857_;
v___y_3826_ = v___y_3851_;
v___y_3827_ = v___y_3846_;
v___y_3828_ = v___y_3855_;
v___y_3829_ = v___y_3852_;
v___y_3830_ = v___y_3853_;
v___y_3831_ = v___y_3854_;
v___y_3832_ = v___y_3856_;
v___y_3833_ = v___y_3849_;
v___y_3834_ = v___y_3850_;
v___y_3835_ = v___y_3858_;
goto v___jp_3821_;
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v___y_3859_);
lean_dec_ref(v___y_3847_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3862_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3862_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
v___jp_3871_:
{
lean_object* v_specs_3883_; lean_object* v_jps_3884_; lean_object* v_lastLiftedPre_x3f_3885_; lean_object* v_nextDeclIdx_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3946_; 
v_specs_3883_ = lean_ctor_get(v_scope_3575_, 0);
v_jps_3884_ = lean_ctor_get(v_scope_3575_, 1);
v_lastLiftedPre_x3f_3885_ = lean_ctor_get(v_scope_3575_, 2);
v_nextDeclIdx_3886_ = lean_ctor_get(v_scope_3575_, 3);
v_isSharedCheck_3946_ = !lean_is_exclusive(v_scope_3575_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3888_ = v_scope_3575_;
v_isShared_3889_ = v_isSharedCheck_3946_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_nextDeclIdx_3886_);
lean_inc(v_lastLiftedPre_x3f_3885_);
lean_inc(v_jps_3884_);
lean_inc(v_specs_3883_);
lean_dec(v_scope_3575_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3946_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3577_);
lean_inc_ref(v___x_3890_);
v___x_3891_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(v_specs_3883_, v___x_3890_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; lean_object* v_fst_3893_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_fst_3893_ = lean_ctor_get(v_a_3892_, 0);
lean_inc(v_fst_3893_);
if (lean_obj_tag(v_fst_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_dec(v_a_3892_);
lean_del_object(v___x_3888_);
lean_dec(v_nextDeclIdx_3886_);
lean_dec(v_lastLiftedPre_x3f_3885_);
lean_dec(v_jps_3884_);
lean_dec(v_goal_3576_);
v_a_3894_ = lean_ctor_get(v_fst_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v_fst_3893_, 1);
v___x_3895_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_3577_);
lean_dec_ref(v_info_3577_);
v___x_3896_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3890_, v___x_3895_, v_a_3894_, v___y_3872_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_);
return v___x_3896_;
}
else
{
lean_object* v_options_3897_; lean_object* v_snd_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3936_; 
v_options_3897_ = lean_ctor_get(v___y_3881_, 2);
v_snd_3898_ = lean_ctor_get(v_a_3892_, 1);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_a_3892_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v_a_3892_, 0);
lean_dec(v_unused_3937_);
v___x_3900_ = v_a_3892_;
v_isShared_3901_ = v_isSharedCheck_3936_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_snd_3898_);
lean_dec(v_a_3892_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3936_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_a_3902_; lean_object* v_inheritedTraceOptions_3903_; uint8_t v_hasTrace_3904_; lean_object* v___x_3906_; 
v_a_3902_ = lean_ctor_get(v_fst_3893_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v_fst_3893_, 1);
v_inheritedTraceOptions_3903_ = lean_ctor_get(v___y_3881_, 13);
v_hasTrace_3904_ = lean_ctor_get_uint8(v_options_3897_, sizeof(void*)*1);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v_snd_3898_);
v___x_3906_ = v___x_3888_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_snd_3898_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v_jps_3884_);
lean_ctor_set(v_reuseFailAlloc_3935_, 2, v_lastLiftedPre_x3f_3885_);
lean_ctor_set(v_reuseFailAlloc_3935_, 3, v_nextDeclIdx_3886_);
v___x_3906_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
if (v_hasTrace_3904_ == 0)
{
lean_del_object(v___x_3900_);
v___y_3822_ = v___x_3906_;
v___y_3823_ = v_a_3902_;
v___y_3824_ = v___x_3890_;
v___y_3825_ = v___y_3872_;
v___y_3826_ = v___y_3873_;
v___y_3827_ = v___y_3874_;
v___y_3828_ = v___y_3875_;
v___y_3829_ = v___y_3876_;
v___y_3830_ = v___y_3877_;
v___y_3831_ = v___y_3878_;
v___y_3832_ = v___y_3879_;
v___y_3833_ = v___y_3880_;
v___y_3834_ = v___y_3881_;
v___y_3835_ = v___y_3882_;
goto v___jp_3821_;
}
else
{
lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3903_, v_options_3897_, v___x_3907_);
if (v___x_3908_ == 0)
{
lean_del_object(v___x_3900_);
v___y_3822_ = v___x_3906_;
v___y_3823_ = v_a_3902_;
v___y_3824_ = v___x_3890_;
v___y_3825_ = v___y_3872_;
v___y_3826_ = v___y_3873_;
v___y_3827_ = v___y_3874_;
v___y_3828_ = v___y_3875_;
v___y_3829_ = v___y_3876_;
v___y_3830_ = v___y_3877_;
v___y_3831_ = v___y_3878_;
v___y_3832_ = v___y_3879_;
v___y_3833_ = v___y_3880_;
v___y_3834_ = v___y_3881_;
v___y_3835_ = v___y_3882_;
goto v___jp_3821_;
}
else
{
lean_object* v_proof_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3913_; 
v_proof_3909_ = lean_ctor_get(v_a_3902_, 1);
v___x_3910_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
lean_inc_ref(v___x_3890_);
v___x_3911_ = l_Lean_MessageData_ofExpr(v___x_3890_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set_tag(v___x_3900_, 7);
lean_ctor_set(v___x_3900_, 1, v___x_3911_);
lean_ctor_set(v___x_3900_, 0, v___x_3910_);
v___x_3913_ = v___x_3900_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3914_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_3915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
switch(lean_obj_tag(v_proof_3909_))
{
case 0:
{
lean_object* v_declName_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_declName_3916_ = lean_ctor_get(v_proof_3909_, 0);
v___x_3917_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3916_);
v___x_3918_ = l_Lean_MessageData_ofName(v_declName_3916_);
v___x_3919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3919_, 0, v___x_3917_);
lean_ctor_set(v___x_3919_, 1, v___x_3918_);
v___y_3845_ = v___x_3906_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v_a_3902_;
v___y_3848_ = v___x_3915_;
v___y_3849_ = v___y_3880_;
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3873_;
v___y_3852_ = v___y_3876_;
v___y_3853_ = v___y_3877_;
v___y_3854_ = v___y_3878_;
v___y_3855_ = v___y_3875_;
v___y_3856_ = v___y_3879_;
v___y_3857_ = v___y_3872_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___x_3890_;
v___y_3860_ = v___x_3919_;
goto v___jp_3844_;
}
case 1:
{
lean_object* v_fvarId_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_fvarId_3920_ = lean_ctor_get(v_proof_3909_, 0);
v___x_3921_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3920_);
v___x_3922_ = l_Lean_mkFVar(v_fvarId_3920_);
v___x_3923_ = l_Lean_MessageData_ofExpr(v___x_3922_);
v___x_3924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3921_);
lean_ctor_set(v___x_3924_, 1, v___x_3923_);
v___y_3845_ = v___x_3906_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v_a_3902_;
v___y_3848_ = v___x_3915_;
v___y_3849_ = v___y_3880_;
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3873_;
v___y_3852_ = v___y_3876_;
v___y_3853_ = v___y_3877_;
v___y_3854_ = v___y_3878_;
v___y_3855_ = v___y_3875_;
v___y_3856_ = v___y_3879_;
v___y_3857_ = v___y_3872_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___x_3890_;
v___y_3860_ = v___x_3924_;
goto v___jp_3844_;
}
default: 
{
lean_object* v_ref_3925_; lean_object* v_proof_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_ref_3925_ = lean_ctor_get(v_proof_3909_, 1);
v_proof_3926_ = lean_ctor_get(v_proof_3909_, 2);
v___x_3927_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3925_);
v___x_3928_ = l_Lean_MessageData_ofSyntax(v_ref_3925_);
v___x_3929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3927_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3929_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
lean_inc_ref(v_proof_3926_);
v___x_3932_ = l_Lean_MessageData_ofExpr(v_proof_3926_);
v___x_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3931_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___y_3845_ = v___x_3906_;
v___y_3846_ = v___y_3874_;
v___y_3847_ = v_a_3902_;
v___y_3848_ = v___x_3915_;
v___y_3849_ = v___y_3880_;
v___y_3850_ = v___y_3881_;
v___y_3851_ = v___y_3873_;
v___y_3852_ = v___y_3876_;
v___y_3853_ = v___y_3877_;
v___y_3854_ = v___y_3878_;
v___y_3855_ = v___y_3875_;
v___y_3856_ = v___y_3879_;
v___y_3857_ = v___y_3872_;
v___y_3858_ = v___y_3882_;
v___y_3859_ = v___x_3890_;
v___y_3860_ = v___x_3933_;
goto v___jp_3844_;
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
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v___x_3890_);
lean_del_object(v___x_3888_);
lean_dec(v_nextDeclIdx_3886_);
lean_dec(v_lastLiftedPre_x3f_3885_);
lean_dec(v_jps_3884_);
lean_dec_ref(v_info_3577_);
lean_dec(v_goal_3576_);
v_a_3938_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3891_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3891_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object* v_scope_3970_, lean_object* v_goal_3971_, lean_object* v_info_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_3970_, v_goal_3971_, v_info_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec(v_a_3974_);
lean_dec_ref(v_a_3973_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(lean_object* v_d_3986_, lean_object* v_writeback_3987_, lean_object* v_m_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
if (lean_obj_tag(v_d_3986_) == 0)
{
lean_object* v_elabFn_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4027_; 
v_elabFn_4001_ = lean_ctor_get(v_d_3986_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_d_3986_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4003_ = v_d_3986_;
v_isShared_4004_ = v_isSharedCheck_4027_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_elabFn_4001_);
lean_dec(v_d_3986_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4027_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4005_; 
lean_inc(v___y_3999_);
lean_inc_ref(v___y_3998_);
lean_inc(v___y_3997_);
lean_inc_ref(v___y_3996_);
v___x_4005_ = lean_apply_6(v_elabFn_4001_, v_m_3988_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, lean_box(0));
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4008_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc_n(v_a_4006_, 2);
lean_dec_ref_known(v___x_4005_, 1);
if (v_isShared_4004_ == 0)
{
lean_ctor_set_tag(v___x_4003_, 1);
lean_ctor_set(v___x_4003_, 0, v_a_4006_);
v___x_4008_ = v___x_4003_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4006_);
v___x_4008_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4009_; 
lean_inc(v___y_3999_);
lean_inc_ref(v___y_3998_);
lean_inc(v___y_3997_);
lean_inc_ref(v___y_3996_);
lean_inc(v___y_3995_);
lean_inc_ref(v___y_3994_);
lean_inc(v___y_3993_);
lean_inc_ref(v___y_3992_);
lean_inc(v___y_3991_);
lean_inc(v___y_3990_);
lean_inc_ref(v___y_3989_);
v___x_4009_ = lean_apply_13(v_writeback_3987_, v___x_4008_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, lean_box(0));
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4016_ == 0)
{
lean_object* v_unused_4017_; 
v_unused_4017_ = lean_ctor_get(v___x_4009_, 0);
lean_dec(v_unused_4017_);
v___x_4011_ = v___x_4009_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_dec(v___x_4009_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v_a_4006_);
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4006_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
lean_dec(v_a_4006_);
v_a_4018_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4009_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4009_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
else
{
lean_del_object(v___x_4003_);
lean_dec_ref(v_writeback_3987_);
return v___x_4005_;
}
}
}
else
{
lean_object* v_value_4028_; lean_object* v___x_4029_; 
lean_dec_ref(v_m_3988_);
lean_dec_ref(v_writeback_3987_);
v_value_4028_ = lean_ctor_get(v_d_3986_, 0);
lean_inc(v_value_4028_);
lean_dec_ref_known(v_d_3986_, 1);
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v_value_4028_);
return v___x_4029_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg___boxed(lean_object* v_d_4030_, lean_object* v_writeback_4031_, lean_object* v_m_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v_d_4030_, v_writeback_4031_, v_m_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0(lean_object* v_00_u03b1_4046_, lean_object* v_d_4047_, lean_object* v_writeback_4048_, lean_object* v_m_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v_d_4047_, v_writeback_4048_, v_m_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___boxed(lean_object* v_00_u03b1_4063_, lean_object* v_d_4064_, lean_object* v_writeback_4065_, lean_object* v_m_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0(v_00_u03b1_4063_, v_d_4064_, v_writeback_4065_, v_m_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_, v___y_4077_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0(lean_object* v_val_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_){
_start:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = lean_st_ref_set(v_val_4080_, v___y_4081_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v___x_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0___boxed(lean_object* v_val_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0(v_val_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v_val_4096_);
return v_res_4110_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__0));
v___x_4113_ = l_Lean_stringToMessageData(v___x_4112_);
return v___x_4113_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3(void){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__2));
v___x_4116_ = l_Lean_stringToMessageData(v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object* v_m_4117_, lean_object* v_prog_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
lean_object* v_untilPat_x3f_4131_; 
v_untilPat_x3f_4131_ = lean_ctor_get(v_a_4119_, 3);
if (lean_obj_tag(v_untilPat_x3f_4131_) == 1)
{
lean_object* v_val_4132_; lean_object* v___x_4133_; lean_object* v___f_4134_; lean_object* v___x_4135_; 
v_val_4132_ = lean_ctor_get(v_untilPat_x3f_4131_, 0);
v___x_4133_ = lean_st_ref_get(v_val_4132_);
lean_inc(v_val_4132_);
v___f_4134_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0___boxed), 14, 1);
lean_closure_set(v___f_4134_, 0, v_val_4132_);
v___x_4135_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v___x_4133_, v___f_4134_, v_m_4117_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; uint8_t v___x_4137_; lean_object* v___x_4138_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = 1;
lean_inc_ref(v_prog_4118_);
v___x_4138_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_a_4136_, v_prog_4118_, v___x_4137_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4185_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4141_ = v___x_4138_;
v_isShared_4142_ = v_isSharedCheck_4185_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4138_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4185_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
if (lean_obj_tag(v_a_4139_) == 0)
{
uint8_t v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
lean_dec_ref(v_prog_4118_);
v___x_4143_ = 0;
v___x_4144_ = lean_box(v___x_4143_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4144_);
v___x_4146_ = v___x_4141_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
else
{
lean_object* v_options_4148_; uint8_t v_hasTrace_4149_; 
lean_dec_ref_known(v_a_4139_, 1);
v_options_4148_ = lean_ctor_get(v_a_4128_, 2);
v_hasTrace_4149_ = lean_ctor_get_uint8(v_options_4148_, sizeof(void*)*1);
if (v_hasTrace_4149_ == 0)
{
lean_object* v___x_4150_; lean_object* v___x_4152_; 
lean_dec_ref(v_prog_4118_);
v___x_4150_ = lean_box(v___x_4137_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4150_);
v___x_4152_ = v___x_4141_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; 
v_inheritedTraceOptions_4154_ = lean_ctor_get(v_a_4128_, 13);
v___x_4155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4156_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4154_, v_options_4148_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec_ref(v_prog_4118_);
v___x_4158_ = lean_box(v___x_4137_);
if (v_isShared_4142_ == 0)
{
lean_ctor_set(v___x_4141_, 0, v___x_4158_);
v___x_4160_ = v___x_4141_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_del_object(v___x_4141_);
v___x_4162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1);
v___x_4163_ = l_Lean_MessageData_ofExpr(v_prog_4118_);
v___x_4164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4162_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3);
v___x_4166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4164_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4155_, v___x_4166_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
if (lean_obj_tag(v___x_4167_) == 0)
{
lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4175_; 
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4175_ == 0)
{
lean_object* v_unused_4176_; 
v_unused_4176_ = lean_ctor_get(v___x_4167_, 0);
lean_dec(v_unused_4176_);
v___x_4169_ = v___x_4167_;
v_isShared_4170_ = v_isSharedCheck_4175_;
goto v_resetjp_4168_;
}
else
{
lean_dec(v___x_4167_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4175_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4171_; lean_object* v___x_4173_; 
v___x_4171_ = lean_box(v___x_4137_);
if (v_isShared_4170_ == 0)
{
lean_ctor_set(v___x_4169_, 0, v___x_4171_);
v___x_4173_ = v___x_4169_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
else
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
v_a_4177_ = lean_ctor_get(v___x_4167_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_4167_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___x_4167_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4167_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
return v___x_4182_;
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
lean_object* v_a_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4193_; 
lean_dec_ref(v_prog_4118_);
v_a_4186_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4193_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4193_ == 0)
{
v___x_4188_ = v___x_4138_;
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_a_4186_);
lean_dec(v___x_4138_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4193_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___x_4191_; 
if (v_isShared_4189_ == 0)
{
v___x_4191_ = v___x_4188_;
goto v_reusejp_4190_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v_a_4186_);
v___x_4191_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4190_;
}
v_reusejp_4190_:
{
return v___x_4191_;
}
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v_prog_4118_);
v_a_4194_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4135_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4135_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
else
{
uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
lean_dec_ref(v_prog_4118_);
lean_dec_ref(v_m_4117_);
v___x_4202_ = 0;
v___x_4203_ = lean_box(v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object* v_m_4205_, lean_object* v_prog_4206_, lean_object* v_a_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v_m_4205_, v_prog_4206_, v_a_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
lean_dec(v_a_4209_);
lean_dec(v_a_4208_);
lean_dec_ref(v_a_4207_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v_b_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___x_4234_; 
lean_inc(v___y_4232_);
lean_inc_ref(v___y_4231_);
lean_inc(v___y_4230_);
lean_inc_ref(v___y_4229_);
lean_inc(v___y_4227_);
lean_inc_ref(v___y_4226_);
lean_inc(v___y_4225_);
lean_inc_ref(v___y_4224_);
lean_inc(v___y_4223_);
lean_inc(v___y_4222_);
lean_inc_ref(v___y_4221_);
v___x_4234_ = lean_apply_13(v_k_4220_, v_b_4228_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, lean_box(0));
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v_b_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v_res_4249_; 
v_res_4249_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v_b_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_);
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec(v___y_4240_);
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4250_, lean_object* v_type_4251_, lean_object* v_val_4252_, lean_object* v_k_4253_, uint8_t v_nondep_4254_, uint8_t v_kind_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___f_4268_; lean_object* v___x_4269_; 
lean_inc(v___y_4262_);
lean_inc_ref(v___y_4261_);
lean_inc(v___y_4260_);
lean_inc_ref(v___y_4259_);
lean_inc(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
v___f_4268_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4268_, 0, v_k_4253_);
lean_closure_set(v___f_4268_, 1, v___y_4256_);
lean_closure_set(v___f_4268_, 2, v___y_4257_);
lean_closure_set(v___f_4268_, 3, v___y_4258_);
lean_closure_set(v___f_4268_, 4, v___y_4259_);
lean_closure_set(v___f_4268_, 5, v___y_4260_);
lean_closure_set(v___f_4268_, 6, v___y_4261_);
lean_closure_set(v___f_4268_, 7, v___y_4262_);
v___x_4269_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4250_, v_type_4251_, v_val_4252_, v___f_4268_, v_nondep_4254_, v_kind_4255_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
if (lean_obj_tag(v___x_4269_) == 0)
{
return v___x_4269_;
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4278_ = _args[0];
lean_object* v_type_4279_ = _args[1];
lean_object* v_val_4280_ = _args[2];
lean_object* v_k_4281_ = _args[3];
lean_object* v_nondep_4282_ = _args[4];
lean_object* v_kind_4283_ = _args[5];
lean_object* v___y_4284_ = _args[6];
lean_object* v___y_4285_ = _args[7];
lean_object* v___y_4286_ = _args[8];
lean_object* v___y_4287_ = _args[9];
lean_object* v___y_4288_ = _args[10];
lean_object* v___y_4289_ = _args[11];
lean_object* v___y_4290_ = _args[12];
lean_object* v___y_4291_ = _args[13];
lean_object* v___y_4292_ = _args[14];
lean_object* v___y_4293_ = _args[15];
lean_object* v___y_4294_ = _args[16];
lean_object* v___y_4295_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4296_; uint8_t v_kind_boxed_4297_; lean_object* v_res_4298_; 
v_nondep_boxed_4296_ = lean_unbox(v_nondep_4282_);
v_kind_boxed_4297_ = lean_unbox(v_kind_4283_);
v_res_4298_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4278_, v_type_4279_, v_val_4280_, v_k_4281_, v_nondep_boxed_4296_, v_kind_boxed_4297_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
lean_dec(v___y_4294_);
lean_dec_ref(v___y_4293_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec(v___y_4285_);
lean_dec_ref(v___y_4284_);
return v_res_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4299_, lean_object* v_name_4300_, lean_object* v_type_4301_, lean_object* v_val_4302_, lean_object* v_k_4303_, uint8_t v_nondep_4304_, uint8_t v_kind_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v___x_4318_; 
v___x_4318_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4300_, v_type_4301_, v_val_4302_, v_k_4303_, v_nondep_4304_, v_kind_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4319_ = _args[0];
lean_object* v_name_4320_ = _args[1];
lean_object* v_type_4321_ = _args[2];
lean_object* v_val_4322_ = _args[3];
lean_object* v_k_4323_ = _args[4];
lean_object* v_nondep_4324_ = _args[5];
lean_object* v_kind_4325_ = _args[6];
lean_object* v___y_4326_ = _args[7];
lean_object* v___y_4327_ = _args[8];
lean_object* v___y_4328_ = _args[9];
lean_object* v___y_4329_ = _args[10];
lean_object* v___y_4330_ = _args[11];
lean_object* v___y_4331_ = _args[12];
lean_object* v___y_4332_ = _args[13];
lean_object* v___y_4333_ = _args[14];
lean_object* v___y_4334_ = _args[15];
lean_object* v___y_4335_ = _args[16];
lean_object* v___y_4336_ = _args[17];
lean_object* v___y_4337_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4338_; uint8_t v_kind_boxed_4339_; lean_object* v_res_4340_; 
v_nondep_boxed_4338_ = lean_unbox(v_nondep_4324_);
v_kind_boxed_4339_ = lean_unbox(v_kind_4325_);
v_res_4340_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4319_, v_name_4320_, v_type_4321_, v_val_4322_, v_k_4323_, v_nondep_boxed_4338_, v_kind_boxed_4339_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4341_, lean_object* v_declInfos_4342_, lean_object* v_k_4343_, lean_object* v_fv_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_){
_start:
{
lean_object* v_res_4357_; 
v_res_4357_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4341_, v_declInfos_4342_, v_k_4343_, v_fv_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
lean_dec(v___y_4355_);
lean_dec_ref(v___y_4354_);
lean_dec(v___y_4353_);
lean_dec_ref(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
return v_res_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4358_, lean_object* v_k_4359_, lean_object* v_acc_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; uint8_t v___x_4375_; 
v___x_4373_ = lean_array_get_size(v_acc_4360_);
v___x_4374_ = lean_array_get_size(v_declInfos_4358_);
v___x_4375_ = lean_nat_dec_lt(v___x_4373_, v___x_4374_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4376_; 
lean_dec_ref(v_declInfos_4358_);
lean_inc(v_a_4371_);
lean_inc_ref(v_a_4370_);
lean_inc(v_a_4369_);
lean_inc_ref(v_a_4368_);
lean_inc(v_a_4367_);
lean_inc_ref(v_a_4366_);
lean_inc(v_a_4365_);
lean_inc_ref(v_a_4364_);
lean_inc(v_a_4363_);
lean_inc(v_a_4362_);
lean_inc_ref(v_a_4361_);
v___x_4376_ = lean_apply_13(v_k_4359_, v_acc_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, lean_box(0));
return v___x_4376_;
}
else
{
lean_object* v___x_4377_; lean_object* v_snd_4378_; lean_object* v_fst_4379_; lean_object* v_fst_4380_; lean_object* v_snd_4381_; lean_object* v___f_4382_; uint8_t v___x_4383_; uint8_t v___x_4384_; lean_object* v___x_4385_; 
v___x_4377_ = lean_array_fget_borrowed(v_declInfos_4358_, v___x_4373_);
v_snd_4378_ = lean_ctor_get(v___x_4377_, 1);
v_fst_4379_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_fst_4379_);
v_fst_4380_ = lean_ctor_get(v_snd_4378_, 0);
lean_inc(v_fst_4380_);
v_snd_4381_ = lean_ctor_get(v_snd_4378_, 1);
lean_inc(v_snd_4381_);
v___f_4382_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4382_, 0, v_acc_4360_);
lean_closure_set(v___f_4382_, 1, v_declInfos_4358_);
lean_closure_set(v___f_4382_, 2, v_k_4359_);
v___x_4383_ = 0;
v___x_4384_ = 0;
v___x_4385_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4379_, v_fst_4380_, v_snd_4381_, v___f_4382_, v___x_4383_, v___x_4384_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
return v___x_4385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4386_, lean_object* v_declInfos_4387_, lean_object* v_k_4388_, lean_object* v_fv_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = lean_array_push(v_acc_4386_, v_fv_4389_);
v___x_4403_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4387_, v_k_4388_, v___x_4402_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4404_, lean_object* v_k_4405_, lean_object* v_acc_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4404_, v_k_4405_, v_acc_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_a_4415_);
lean_dec_ref(v_a_4414_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
lean_dec(v_a_4411_);
lean_dec_ref(v_a_4410_);
lean_dec(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec_ref(v_a_4407_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4420_, lean_object* v_h__1_4421_){
_start:
{
lean_object* v_snd_4422_; lean_object* v_fst_4423_; lean_object* v_fst_4424_; lean_object* v_snd_4425_; lean_object* v___x_4426_; 
v_snd_4422_ = lean_ctor_get(v_x_4420_, 1);
lean_inc(v_snd_4422_);
v_fst_4423_ = lean_ctor_get(v_x_4420_, 0);
lean_inc(v_fst_4423_);
lean_dec_ref(v_x_4420_);
v_fst_4424_ = lean_ctor_get(v_snd_4422_, 0);
lean_inc(v_fst_4424_);
v_snd_4425_ = lean_ctor_get(v_snd_4422_, 1);
lean_inc(v_snd_4425_);
lean_dec(v_snd_4422_);
v___x_4426_ = lean_apply_3(v_h__1_4421_, v_fst_4423_, v_fst_4424_, v_snd_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4427_, lean_object* v_x_4428_, lean_object* v_h__1_4429_){
_start:
{
lean_object* v_snd_4430_; lean_object* v_fst_4431_; lean_object* v_fst_4432_; lean_object* v_snd_4433_; lean_object* v___x_4434_; 
v_snd_4430_ = lean_ctor_get(v_x_4428_, 1);
lean_inc(v_snd_4430_);
v_fst_4431_ = lean_ctor_get(v_x_4428_, 0);
lean_inc(v_fst_4431_);
lean_dec_ref(v_x_4428_);
v_fst_4432_ = lean_ctor_get(v_snd_4430_, 0);
lean_inc(v_fst_4432_);
v_snd_4433_ = lean_ctor_get(v_snd_4430_, 1);
lean_inc(v_snd_4433_);
lean_dec(v_snd_4430_);
v___x_4434_ = lean_apply_3(v_h__1_4429_, v_fst_4431_, v_fst_4432_, v_snd_4433_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(lean_object* v_declInfos_4437_, lean_object* v_k_4438_, lean_object* v_a_4439_, lean_object* v_a_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4451_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0));
v___x_4452_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4437_, v_k_4438_, v___x_4451_, v_a_4439_, v_a_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_, v_a_4448_, v_a_4449_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4453_, lean_object* v_k_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v_res_4467_; 
v_res_4467_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(v_declInfos_4453_, v_k_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_, v_a_4465_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
lean_dec(v_a_4459_);
lean_dec_ref(v_a_4458_);
lean_dec(v_a_4457_);
lean_dec(v_a_4456_);
lean_dec_ref(v_a_4455_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object* v_e_4468_, lean_object* v___y_4469_){
_start:
{
uint8_t v___x_4471_; 
v___x_4471_ = l_Lean_Expr_hasMVar(v_e_4468_);
if (v___x_4471_ == 0)
{
lean_object* v___x_4472_; 
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v_e_4468_);
return v___x_4472_;
}
else
{
lean_object* v___x_4473_; lean_object* v_mctx_4474_; lean_object* v___x_4475_; lean_object* v_fst_4476_; lean_object* v_snd_4477_; lean_object* v___x_4478_; lean_object* v_cache_4479_; lean_object* v_zetaDeltaFVarIds_4480_; lean_object* v_postponed_4481_; lean_object* v_diag_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4491_; 
v___x_4473_ = lean_st_ref_get(v___y_4469_);
v_mctx_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc_ref(v_mctx_4474_);
lean_dec(v___x_4473_);
v___x_4475_ = l_Lean_instantiateMVarsCore(v_mctx_4474_, v_e_4468_);
v_fst_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_fst_4476_);
v_snd_4477_ = lean_ctor_get(v___x_4475_, 1);
lean_inc(v_snd_4477_);
lean_dec_ref(v___x_4475_);
v___x_4478_ = lean_st_ref_take(v___y_4469_);
v_cache_4479_ = lean_ctor_get(v___x_4478_, 1);
v_zetaDeltaFVarIds_4480_ = lean_ctor_get(v___x_4478_, 2);
v_postponed_4481_ = lean_ctor_get(v___x_4478_, 3);
v_diag_4482_ = lean_ctor_get(v___x_4478_, 4);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4491_ == 0)
{
lean_object* v_unused_4492_; 
v_unused_4492_ = lean_ctor_get(v___x_4478_, 0);
lean_dec(v_unused_4492_);
v___x_4484_ = v___x_4478_;
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_diag_4482_);
lean_inc(v_postponed_4481_);
lean_inc(v_zetaDeltaFVarIds_4480_);
lean_inc(v_cache_4479_);
lean_dec(v___x_4478_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v_snd_4477_);
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_snd_4477_);
lean_ctor_set(v_reuseFailAlloc_4490_, 1, v_cache_4479_);
lean_ctor_set(v_reuseFailAlloc_4490_, 2, v_zetaDeltaFVarIds_4480_);
lean_ctor_set(v_reuseFailAlloc_4490_, 3, v_postponed_4481_);
lean_ctor_set(v_reuseFailAlloc_4490_, 4, v_diag_4482_);
v___x_4487_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; 
v___x_4488_ = lean_st_ref_set(v___y_4469_, v___x_4487_);
v___x_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4489_, 0, v_fst_4476_);
return v___x_4489_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_e_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_e_4493_, v___y_4494_);
lean_dec(v___y_4494_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object* v_e_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v___x_4505_; 
v___x_4505_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_e_4497_, v___y_4501_);
return v___x_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object* v_e_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(v_e_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4514_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object* v_x_4515_){
_start:
{
uint8_t v___x_4516_; 
v___x_4516_ = 0;
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4517_){
_start:
{
uint8_t v_res_4518_; lean_object* v_r_4519_; 
v_res_4518_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(v_x_4517_);
lean_dec(v_x_4517_);
v_r_4519_ = lean_box(v_res_4518_);
return v_r_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4520_, lean_object* v___x_4521_, uint8_t v___x_4522_, lean_object* v___x_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4520_, v___x_4521_, v___x_4522_, v___x_4522_, v___x_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; uint8_t v___x_4533_; lean_object* v___x_4534_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = 0;
v___x_4534_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4533_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_object* v___x_4535_; 
lean_dec_ref_known(v___x_4534_, 1);
v___x_4535_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_a_4532_, v___y_4527_);
return v___x_4535_;
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_dec(v_a_4532_);
v_a_4536_ = lean_ctor_get(v___x_4534_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4534_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4534_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4534_);
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
else
{
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4544_, lean_object* v___x_4545_, lean_object* v___x_4546_, lean_object* v___x_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
uint8_t v___x_13995__boxed_4555_; lean_object* v_res_4556_; 
v___x_13995__boxed_4555_ = lean_unbox(v___x_4546_);
v_res_4556_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(v_frameStx_4544_, v___x_4545_, v___x_13995__boxed_4555_, v___x_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
return v_res_4556_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object* v_info_4562_, lean_object* v_frameStx_4563_, lean_object* v___f_4564_, lean_object* v_fvs_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_){
_start:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; uint8_t v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___f_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; uint8_t v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4578_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_4562_);
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
v___x_4580_ = 1;
v___x_4581_ = lean_box(0);
v___x_4582_ = lean_box(v___x_4580_);
v___f_4583_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4583_, 0, v_frameStx_4563_);
lean_closure_set(v___f_4583_, 1, v___x_4579_);
lean_closure_set(v___f_4583_, 2, v___x_4582_);
lean_closure_set(v___f_4583_, 3, v___x_4581_);
v___x_4584_ = lean_box(0);
v___x_4585_ = lean_box(1);
v___x_4586_ = 0;
v___x_4587_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0));
v___x_4588_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4588_, 0, v___x_4581_);
lean_ctor_set(v___x_4588_, 1, v___x_4584_);
lean_ctor_set(v___x_4588_, 2, v___x_4581_);
lean_ctor_set(v___x_4588_, 3, v___f_4564_);
lean_ctor_set(v___x_4588_, 4, v___x_4585_);
lean_ctor_set(v___x_4588_, 5, v___x_4585_);
lean_ctor_set(v___x_4588_, 6, v___x_4581_);
lean_ctor_set(v___x_4588_, 7, v___x_4587_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8, v___x_4580_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 1, v___x_4580_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 2, v___x_4580_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 3, v___x_4580_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 4, v___x_4586_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 5, v___x_4586_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 6, v___x_4586_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 7, v___x_4586_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 8, v___x_4580_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 9, v___x_4586_);
lean_ctor_set_uint8(v___x_4588_, sizeof(void*)*8 + 10, v___x_4580_);
v___x_4589_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1));
v___x_4590_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4583_, v___x_4588_, v___x_4589_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
if (lean_obj_tag(v___x_4590_) == 0)
{
lean_object* v_a_4591_; lean_object* v_fst_4592_; uint8_t v___x_4593_; lean_object* v___x_4594_; 
v_a_4591_ = lean_ctor_get(v___x_4590_, 0);
lean_inc(v_a_4591_);
lean_dec_ref_known(v___x_4590_, 1);
v_fst_4592_ = lean_ctor_get(v_a_4591_, 0);
lean_inc(v_fst_4592_);
lean_dec(v_a_4591_);
v___x_4593_ = 1;
v___x_4594_ = l_Lean_Meta_mkLetFVars(v_fvs_4565_, v_fst_4592_, v___x_4580_, v___x_4580_, v___x_4593_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
return v___x_4594_;
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4602_; 
v_a_4595_ = lean_ctor_get(v___x_4590_, 0);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4590_);
if (v_isSharedCheck_4602_ == 0)
{
v___x_4597_ = v___x_4590_;
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_a_4595_);
lean_dec(v___x_4590_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4602_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
lean_object* v___x_4600_; 
if (v_isShared_4598_ == 0)
{
v___x_4600_ = v___x_4597_;
goto v_reusejp_4599_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
v___x_4600_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4599_;
}
v_reusejp_4599_:
{
return v___x_4600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object* v_info_4603_, lean_object* v_frameStx_4604_, lean_object* v___f_4605_, lean_object* v_fvs_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(v_info_4603_, v_frameStx_4604_, v___f_4605_, v_fvs_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
lean_dec_ref(v_fvs_4606_);
lean_dec_ref(v_info_4603_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(lean_object* v___x_4620_, lean_object* v_res_4621_, lean_object* v_range_4622_, lean_object* v_b_4623_, lean_object* v_i_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
lean_object* v_stop_4630_; lean_object* v_step_4631_; lean_object* v_a_4633_; uint8_t v___x_4636_; 
v_stop_4630_ = lean_ctor_get(v_range_4622_, 1);
v_step_4631_ = lean_ctor_get(v_range_4622_, 2);
v___x_4636_ = lean_nat_dec_lt(v_i_4624_, v_stop_4630_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
lean_dec(v_i_4624_);
v___x_4637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4637_, 0, v_b_4623_);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; 
v___x_4638_ = lean_array_fget_borrowed(v___x_4620_, v_i_4624_);
if (lean_obj_tag(v___x_4638_) == 1)
{
lean_object* v_val_4639_; lean_object* v_args_4640_; lean_object* v___x_4641_; uint8_t v___x_4642_; 
v_val_4639_ = lean_ctor_get(v___x_4638_, 0);
v_args_4640_ = lean_ctor_get(v_res_4621_, 1);
v___x_4641_ = lean_array_get_size(v_args_4640_);
v___x_4642_ = lean_nat_dec_lt(v_i_4624_, v___x_4641_);
if (v___x_4642_ == 0)
{
v_a_4633_ = v_b_4623_;
goto v___jp_4632_;
}
else
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4643_ = l_Lean_instInhabitedExpr;
v___x_4644_ = lean_array_get_borrowed(v___x_4643_, v_args_4640_, v_i_4624_);
lean_inc(v___y_4628_);
lean_inc_ref(v___y_4627_);
lean_inc(v___y_4626_);
lean_inc_ref(v___y_4625_);
lean_inc(v___x_4644_);
v___x_4645_ = lean_infer_type(v___x_4644_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
lean_inc(v___x_4644_);
v___x_4647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4647_, 0, v_a_4646_);
lean_ctor_set(v___x_4647_, 1, v___x_4644_);
lean_inc(v_val_4639_);
v___x_4648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4648_, 0, v_val_4639_);
lean_ctor_set(v___x_4648_, 1, v___x_4647_);
v___x_4649_ = lean_array_push(v_b_4623_, v___x_4648_);
v_a_4633_ = v___x_4649_;
goto v___jp_4632_;
}
else
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4657_; 
lean_dec(v_i_4624_);
lean_dec_ref(v_b_4623_);
v_a_4650_ = lean_ctor_get(v___x_4645_, 0);
v_isSharedCheck_4657_ = !lean_is_exclusive(v___x_4645_);
if (v_isSharedCheck_4657_ == 0)
{
v___x_4652_ = v___x_4645_;
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4645_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4657_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4655_; 
if (v_isShared_4653_ == 0)
{
v___x_4655_ = v___x_4652_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_a_4650_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
return v___x_4655_;
}
}
}
}
}
else
{
v_a_4633_ = v_b_4623_;
goto v___jp_4632_;
}
}
v___jp_4632_:
{
lean_object* v___x_4634_; 
v___x_4634_ = lean_nat_add(v_i_4624_, v_step_4631_);
lean_dec(v_i_4624_);
v_b_4623_ = v_a_4633_;
v_i_4624_ = v___x_4634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg___boxed(lean_object* v___x_4658_, lean_object* v_res_4659_, lean_object* v_range_4660_, lean_object* v_b_4661_, lean_object* v_i_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_){
_start:
{
lean_object* v_res_4668_; 
v_res_4668_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(v___x_4658_, v_res_4659_, v_range_4660_, v_b_4661_, v_i_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
lean_dec(v___y_4666_);
lean_dec_ref(v___y_4665_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec_ref(v_range_4660_);
lean_dec_ref(v_res_4659_);
lean_dec_ref(v___x_4658_);
return v_res_4668_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2(void){
_start:
{
uint8_t v___x_4672_; uint64_t v___x_4673_; 
v___x_4672_ = 1;
v___x_4673_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4672_);
return v___x_4673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object* v_entry_4674_, lean_object* v_res_4675_, lean_object* v_info_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_, lean_object* v_a_4681_, lean_object* v_a_4682_, lean_object* v_a_4683_, lean_object* v_a_4684_, lean_object* v_a_4685_, lean_object* v_a_4686_, lean_object* v_a_4687_){
_start:
{
lean_object* v_varNames_4689_; lean_object* v_frameStx_4690_; lean_object* v___x_4691_; lean_object* v_decls_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v_varNames_4689_ = lean_ctor_get(v_entry_4674_, 1);
lean_inc_ref(v_varNames_4689_);
v_frameStx_4690_ = lean_ctor_get(v_entry_4674_, 2);
lean_inc(v_frameStx_4690_);
lean_dec_ref(v_entry_4674_);
v___x_4691_ = lean_unsigned_to_nat(0u);
v_decls_4692_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0));
v___x_4693_ = lean_array_get_size(v_varNames_4689_);
v___x_4694_ = lean_unsigned_to_nat(1u);
v___x_4695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4691_);
lean_ctor_set(v___x_4695_, 1, v___x_4693_);
lean_ctor_set(v___x_4695_, 2, v___x_4694_);
v___x_4696_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(v_varNames_4689_, v_res_4675_, v___x_4695_, v_decls_4692_, v___x_4691_, v_a_4684_, v_a_4685_, v_a_4686_, v_a_4687_);
lean_dec_ref_known(v___x_4695_, 3);
lean_dec_ref(v_varNames_4689_);
if (lean_obj_tag(v___x_4696_) == 0)
{
lean_object* v_a_4697_; lean_object* v___x_4698_; uint8_t v_foApprox_4699_; uint8_t v_ctxApprox_4700_; uint8_t v_quasiPatternApprox_4701_; uint8_t v_constApprox_4702_; uint8_t v_isDefEqStuckEx_4703_; uint8_t v_unificationHints_4704_; uint8_t v_proofIrrelevance_4705_; uint8_t v_assignSyntheticOpaque_4706_; uint8_t v_offsetCnstrs_4707_; uint8_t v_etaStruct_4708_; uint8_t v_univApprox_4709_; uint8_t v_iota_4710_; uint8_t v_beta_4711_; uint8_t v_proj_4712_; uint8_t v_zeta_4713_; uint8_t v_zetaDelta_4714_; uint8_t v_zetaUnused_4715_; uint8_t v_zetaHave_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4753_; 
v_a_4697_ = lean_ctor_get(v___x_4696_, 0);
lean_inc(v_a_4697_);
lean_dec_ref_known(v___x_4696_, 1);
v___x_4698_ = l_Lean_Meta_Context_config(v_a_4684_);
v_foApprox_4699_ = lean_ctor_get_uint8(v___x_4698_, 0);
v_ctxApprox_4700_ = lean_ctor_get_uint8(v___x_4698_, 1);
v_quasiPatternApprox_4701_ = lean_ctor_get_uint8(v___x_4698_, 2);
v_constApprox_4702_ = lean_ctor_get_uint8(v___x_4698_, 3);
v_isDefEqStuckEx_4703_ = lean_ctor_get_uint8(v___x_4698_, 4);
v_unificationHints_4704_ = lean_ctor_get_uint8(v___x_4698_, 5);
v_proofIrrelevance_4705_ = lean_ctor_get_uint8(v___x_4698_, 6);
v_assignSyntheticOpaque_4706_ = lean_ctor_get_uint8(v___x_4698_, 7);
v_offsetCnstrs_4707_ = lean_ctor_get_uint8(v___x_4698_, 8);
v_etaStruct_4708_ = lean_ctor_get_uint8(v___x_4698_, 10);
v_univApprox_4709_ = lean_ctor_get_uint8(v___x_4698_, 11);
v_iota_4710_ = lean_ctor_get_uint8(v___x_4698_, 12);
v_beta_4711_ = lean_ctor_get_uint8(v___x_4698_, 13);
v_proj_4712_ = lean_ctor_get_uint8(v___x_4698_, 14);
v_zeta_4713_ = lean_ctor_get_uint8(v___x_4698_, 15);
v_zetaDelta_4714_ = lean_ctor_get_uint8(v___x_4698_, 16);
v_zetaUnused_4715_ = lean_ctor_get_uint8(v___x_4698_, 17);
v_zetaHave_4716_ = lean_ctor_get_uint8(v___x_4698_, 18);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4718_ = v___x_4698_;
v_isShared_4719_ = v_isSharedCheck_4753_;
goto v_resetjp_4717_;
}
else
{
lean_dec(v___x_4698_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4753_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
uint8_t v_trackZetaDelta_4720_; lean_object* v_zetaDeltaSet_4721_; lean_object* v_lctx_4722_; lean_object* v_localInstances_4723_; lean_object* v_defEqCtx_x3f_4724_; lean_object* v_synthPendingDepth_4725_; lean_object* v_canUnfold_x3f_4726_; uint8_t v_univApprox_4727_; uint8_t v_inTypeClassResolution_4728_; uint8_t v_cacheInferType_4729_; uint8_t v___x_4730_; lean_object* v_config_4732_; 
v_trackZetaDelta_4720_ = lean_ctor_get_uint8(v_a_4684_, sizeof(void*)*7);
v_zetaDeltaSet_4721_ = lean_ctor_get(v_a_4684_, 1);
v_lctx_4722_ = lean_ctor_get(v_a_4684_, 2);
v_localInstances_4723_ = lean_ctor_get(v_a_4684_, 3);
v_defEqCtx_x3f_4724_ = lean_ctor_get(v_a_4684_, 4);
v_synthPendingDepth_4725_ = lean_ctor_get(v_a_4684_, 5);
v_canUnfold_x3f_4726_ = lean_ctor_get(v_a_4684_, 6);
v_univApprox_4727_ = lean_ctor_get_uint8(v_a_4684_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4728_ = lean_ctor_get_uint8(v_a_4684_, sizeof(void*)*7 + 2);
v_cacheInferType_4729_ = lean_ctor_get_uint8(v_a_4684_, sizeof(void*)*7 + 3);
v___x_4730_ = 1;
if (v_isShared_4719_ == 0)
{
v_config_4732_ = v___x_4718_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 0, v_foApprox_4699_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 1, v_ctxApprox_4700_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 2, v_quasiPatternApprox_4701_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 3, v_constApprox_4702_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 4, v_isDefEqStuckEx_4703_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 5, v_unificationHints_4704_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 6, v_proofIrrelevance_4705_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 7, v_assignSyntheticOpaque_4706_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 8, v_offsetCnstrs_4707_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 10, v_etaStruct_4708_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 11, v_univApprox_4709_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 12, v_iota_4710_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 13, v_beta_4711_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 14, v_proj_4712_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 15, v_zeta_4713_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 16, v_zetaDelta_4714_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 17, v_zetaUnused_4715_);
lean_ctor_set_uint8(v_reuseFailAlloc_4752_, 18, v_zetaHave_4716_);
v_config_4732_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
uint64_t v___x_4733_; uint64_t v___x_4734_; uint64_t v___x_4735_; lean_object* v___f_4736_; lean_object* v___f_4737_; uint64_t v___x_4738_; uint64_t v___x_4739_; uint64_t v_key_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
lean_ctor_set_uint8(v_config_4732_, 9, v___x_4730_);
v___x_4733_ = l_Lean_Meta_Context_configKey(v_a_4684_);
v___x_4734_ = 3ULL;
v___x_4735_ = lean_uint64_shift_right(v___x_4733_, v___x_4734_);
v___f_4736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1));
v___f_4737_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4737_, 0, v_info_4676_);
lean_closure_set(v___f_4737_, 1, v_frameStx_4690_);
lean_closure_set(v___f_4737_, 2, v___f_4736_);
v___x_4738_ = lean_uint64_shift_left(v___x_4735_, v___x_4734_);
v___x_4739_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2);
v_key_4740_ = lean_uint64_lor(v___x_4738_, v___x_4739_);
v___x_4741_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4741_, 0, v_config_4732_);
lean_ctor_set_uint64(v___x_4741_, sizeof(void*)*1, v_key_4740_);
lean_inc(v_canUnfold_x3f_4726_);
lean_inc(v_synthPendingDepth_4725_);
lean_inc(v_defEqCtx_x3f_4724_);
lean_inc_ref(v_localInstances_4723_);
lean_inc_ref(v_lctx_4722_);
lean_inc(v_zetaDeltaSet_4721_);
v___x_4742_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4742_, 0, v___x_4741_);
lean_ctor_set(v___x_4742_, 1, v_zetaDeltaSet_4721_);
lean_ctor_set(v___x_4742_, 2, v_lctx_4722_);
lean_ctor_set(v___x_4742_, 3, v_localInstances_4723_);
lean_ctor_set(v___x_4742_, 4, v_defEqCtx_x3f_4724_);
lean_ctor_set(v___x_4742_, 5, v_synthPendingDepth_4725_);
lean_ctor_set(v___x_4742_, 6, v_canUnfold_x3f_4726_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*7, v_trackZetaDelta_4720_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*7 + 1, v_univApprox_4727_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4728_);
lean_ctor_set_uint8(v___x_4742_, sizeof(void*)*7 + 3, v_cacheInferType_4729_);
v___x_4743_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_a_4697_, v___f_4737_, v_decls_4692_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_, v_a_4681_, v_a_4682_, v_a_4683_, v___x_4742_, v_a_4685_, v_a_4686_, v_a_4687_);
lean_dec_ref_known(v___x_4742_, 7);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_object* v_a_4744_; lean_object* v___x_4746_; uint8_t v_isShared_4747_; uint8_t v_isSharedCheck_4751_; 
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
v_isSharedCheck_4751_ = !lean_is_exclusive(v___x_4743_);
if (v_isSharedCheck_4751_ == 0)
{
v___x_4746_ = v___x_4743_;
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
else
{
lean_inc(v_a_4744_);
lean_dec(v___x_4743_);
v___x_4746_ = lean_box(0);
v_isShared_4747_ = v_isSharedCheck_4751_;
goto v_resetjp_4745_;
}
v_resetjp_4745_:
{
lean_object* v___x_4749_; 
if (v_isShared_4747_ == 0)
{
v___x_4749_ = v___x_4746_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4750_; 
v_reuseFailAlloc_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4750_, 0, v_a_4744_);
v___x_4749_ = v_reuseFailAlloc_4750_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
return v___x_4749_;
}
}
}
else
{
return v___x_4743_;
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
lean_dec(v_frameStx_4690_);
lean_dec_ref(v_info_4676_);
v_a_4754_ = lean_ctor_get(v___x_4696_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4696_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4696_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4696_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object* v_entry_4762_, lean_object* v_res_4763_, lean_object* v_info_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_entry_4762_, v_res_4763_, v_info_4764_, v_a_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec_ref(v_res_4763_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1(lean_object* v___x_4778_, lean_object* v_res_4779_, lean_object* v_range_4780_, lean_object* v_b_4781_, lean_object* v_i_4782_, lean_object* v_hs_4783_, lean_object* v_hl_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v___x_4797_; 
v___x_4797_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(v___x_4778_, v_res_4779_, v_range_4780_, v_b_4781_, v_i_4782_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
return v___x_4797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___boxed(lean_object** _args){
lean_object* v___x_4798_ = _args[0];
lean_object* v_res_4799_ = _args[1];
lean_object* v_range_4800_ = _args[2];
lean_object* v_b_4801_ = _args[3];
lean_object* v_i_4802_ = _args[4];
lean_object* v_hs_4803_ = _args[5];
lean_object* v_hl_4804_ = _args[6];
lean_object* v___y_4805_ = _args[7];
lean_object* v___y_4806_ = _args[8];
lean_object* v___y_4807_ = _args[9];
lean_object* v___y_4808_ = _args[10];
lean_object* v___y_4809_ = _args[11];
lean_object* v___y_4810_ = _args[12];
lean_object* v___y_4811_ = _args[13];
lean_object* v___y_4812_ = _args[14];
lean_object* v___y_4813_ = _args[15];
lean_object* v___y_4814_ = _args[16];
lean_object* v___y_4815_ = _args[17];
lean_object* v___y_4816_ = _args[18];
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1(v___x_4798_, v_res_4799_, v_range_4800_, v_b_4801_, v_i_4802_, v_hs_4803_, v_hl_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
lean_dec(v___y_4811_);
lean_dec_ref(v___y_4810_);
lean_dec(v___y_4809_);
lean_dec_ref(v___y_4808_);
lean_dec(v___y_4807_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec_ref(v_range_4800_);
lean_dec_ref(v_res_4799_);
lean_dec_ref(v___x_4798_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0(lean_object* v_d_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v___x_4831_; lean_object* v_specBackwardRuleCache_4832_; lean_object* v_splitBackwardRuleCache_4833_; lean_object* v_latticeBackwardRuleCache_4834_; lean_object* v_invariants_4835_; lean_object* v_vcs_4836_; lean_object* v_simpState_4837_; lean_object* v_fuel_4838_; lean_object* v_inlineHandledInvariants_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4850_; 
v___x_4831_ = lean_st_ref_take(v___y_4820_);
v_specBackwardRuleCache_4832_ = lean_ctor_get(v___x_4831_, 0);
v_splitBackwardRuleCache_4833_ = lean_ctor_get(v___x_4831_, 1);
v_latticeBackwardRuleCache_4834_ = lean_ctor_get(v___x_4831_, 2);
v_invariants_4835_ = lean_ctor_get(v___x_4831_, 4);
v_vcs_4836_ = lean_ctor_get(v___x_4831_, 5);
v_simpState_4837_ = lean_ctor_get(v___x_4831_, 6);
v_fuel_4838_ = lean_ctor_get(v___x_4831_, 7);
v_inlineHandledInvariants_4839_ = lean_ctor_get(v___x_4831_, 8);
v_isSharedCheck_4850_ = !lean_is_exclusive(v___x_4831_);
if (v_isSharedCheck_4850_ == 0)
{
lean_object* v_unused_4851_; 
v_unused_4851_ = lean_ctor_get(v___x_4831_, 3);
lean_dec(v_unused_4851_);
v___x_4841_ = v___x_4831_;
v_isShared_4842_ = v_isSharedCheck_4850_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_inlineHandledInvariants_4839_);
lean_inc(v_fuel_4838_);
lean_inc(v_simpState_4837_);
lean_inc(v_vcs_4836_);
lean_inc(v_invariants_4835_);
lean_inc(v_latticeBackwardRuleCache_4834_);
lean_inc(v_splitBackwardRuleCache_4833_);
lean_inc(v_specBackwardRuleCache_4832_);
lean_dec(v___x_4831_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4850_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4843_; lean_object* v___x_4845_; 
v___x_4843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4843_, 0, v_d_4818_);
if (v_isShared_4842_ == 0)
{
lean_ctor_set(v___x_4841_, 3, v___x_4843_);
v___x_4845_ = v___x_4841_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4849_; 
v_reuseFailAlloc_4849_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4849_, 0, v_specBackwardRuleCache_4832_);
lean_ctor_set(v_reuseFailAlloc_4849_, 1, v_splitBackwardRuleCache_4833_);
lean_ctor_set(v_reuseFailAlloc_4849_, 2, v_latticeBackwardRuleCache_4834_);
lean_ctor_set(v_reuseFailAlloc_4849_, 3, v___x_4843_);
lean_ctor_set(v_reuseFailAlloc_4849_, 4, v_invariants_4835_);
lean_ctor_set(v_reuseFailAlloc_4849_, 5, v_vcs_4836_);
lean_ctor_set(v_reuseFailAlloc_4849_, 6, v_simpState_4837_);
lean_ctor_set(v_reuseFailAlloc_4849_, 7, v_fuel_4838_);
lean_ctor_set(v_reuseFailAlloc_4849_, 8, v_inlineHandledInvariants_4839_);
v___x_4845_ = v_reuseFailAlloc_4849_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4846_ = lean_st_ref_set(v___y_4820_, v___x_4845_);
v___x_4847_ = lean_box(0);
v___x_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
return v___x_4848_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0___boxed(lean_object* v_d_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_){
_start:
{
lean_object* v_res_4865_; 
v_res_4865_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0(v_d_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec(v___y_4855_);
lean_dec(v___y_4854_);
lean_dec_ref(v___y_4853_);
return v_res_4865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v_a_4866_, lean_object* v___x_4867_, lean_object* v_as_4868_, size_t v_sz_4869_, size_t v_i_4870_, lean_object* v_b_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
lean_object* v_a_4880_; uint8_t v___x_4884_; 
v___x_4884_ = lean_usize_dec_lt(v_i_4870_, v_sz_4869_);
if (v___x_4884_ == 0)
{
lean_object* v___x_4885_; 
lean_dec_ref(v___x_4867_);
v___x_4885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_b_4871_);
return v___x_4885_;
}
else
{
lean_object* v_entries_4886_; lean_object* v___x_4887_; lean_object* v_a_4888_; lean_object* v___x_4889_; uint8_t v_retired_4890_; 
v_entries_4886_ = lean_ctor_get(v_a_4866_, 1);
v___x_4887_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
v_a_4888_ = lean_array_uget_borrowed(v_as_4868_, v_i_4870_);
v___x_4889_ = lean_array_get_borrowed(v___x_4887_, v_entries_4886_, v_a_4888_);
v_retired_4890_ = lean_ctor_get_uint8(v___x_4889_, sizeof(void*)*4);
if (v_retired_4890_ == 0)
{
lean_object* v_pat_4891_; lean_object* v_srcIdx_4892_; lean_object* v___x_4893_; 
v_pat_4891_ = lean_ctor_get(v___x_4889_, 0);
v_srcIdx_4892_ = lean_ctor_get(v___x_4889_, 3);
lean_inc_ref(v___x_4867_);
lean_inc_ref(v_pat_4891_);
v___x_4893_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4891_, v___x_4867_, v___x_4884_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v_a_4894_; 
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref_known(v___x_4893_, 1);
if (lean_obj_tag(v_a_4894_) == 1)
{
if (lean_obj_tag(v_b_4871_) == 0)
{
lean_object* v_val_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4903_; 
v_val_4895_ = lean_ctor_get(v_a_4894_, 0);
v_isSharedCheck_4903_ = !lean_is_exclusive(v_a_4894_);
if (v_isSharedCheck_4903_ == 0)
{
v___x_4897_ = v_a_4894_;
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_val_4895_);
lean_dec(v_a_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4903_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; lean_object* v___x_4901_; 
lean_inc(v___x_4889_);
v___x_4899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4899_, 0, v___x_4889_);
lean_ctor_set(v___x_4899_, 1, v_val_4895_);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 0, v___x_4899_);
v___x_4901_ = v___x_4897_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v___x_4899_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
v_a_4880_ = v___x_4901_;
goto v___jp_4879_;
}
}
}
else
{
lean_object* v_val_4904_; lean_object* v_fst_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4923_; 
v_val_4904_ = lean_ctor_get(v_b_4871_, 0);
lean_inc(v_val_4904_);
v_fst_4905_ = lean_ctor_get(v_val_4904_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v_val_4904_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v_val_4904_, 1);
lean_dec(v_unused_4924_);
v___x_4907_ = v_val_4904_;
v_isShared_4908_ = v_isSharedCheck_4923_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_fst_4905_);
lean_dec(v_val_4904_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4923_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v_val_4909_; lean_object* v_srcIdx_4910_; uint8_t v___x_4911_; 
v_val_4909_ = lean_ctor_get(v_a_4894_, 0);
lean_inc(v_val_4909_);
lean_dec_ref_known(v_a_4894_, 1);
v_srcIdx_4910_ = lean_ctor_get(v_fst_4905_, 3);
lean_inc(v_srcIdx_4910_);
lean_dec(v_fst_4905_);
v___x_4911_ = lean_nat_dec_lt(v_srcIdx_4892_, v_srcIdx_4910_);
lean_dec(v_srcIdx_4910_);
if (v___x_4911_ == 0)
{
lean_dec(v_val_4909_);
lean_del_object(v___x_4907_);
v_a_4880_ = v_b_4871_;
goto v___jp_4879_;
}
else
{
lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4921_; 
v_isSharedCheck_4921_ = !lean_is_exclusive(v_b_4871_);
if (v_isSharedCheck_4921_ == 0)
{
lean_object* v_unused_4922_; 
v_unused_4922_ = lean_ctor_get(v_b_4871_, 0);
lean_dec(v_unused_4922_);
v___x_4913_ = v_b_4871_;
v_isShared_4914_ = v_isSharedCheck_4921_;
goto v_resetjp_4912_;
}
else
{
lean_dec(v_b_4871_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4921_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
lean_inc(v___x_4889_);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 1, v_val_4909_);
lean_ctor_set(v___x_4907_, 0, v___x_4889_);
v___x_4916_ = v___x_4907_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_val_4909_);
v___x_4916_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
lean_object* v___x_4918_; 
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 0, v___x_4916_);
v___x_4918_ = v___x_4913_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4919_; 
v_reuseFailAlloc_4919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4919_, 0, v___x_4916_);
v___x_4918_ = v_reuseFailAlloc_4919_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
v_a_4880_ = v___x_4918_;
goto v___jp_4879_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4894_);
v_a_4880_ = v_b_4871_;
goto v___jp_4879_;
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4932_; 
lean_dec(v_b_4871_);
lean_dec_ref(v___x_4867_);
v_a_4925_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4932_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4932_ == 0)
{
v___x_4927_ = v___x_4893_;
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
else
{
lean_inc(v_a_4925_);
lean_dec(v___x_4893_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4932_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
lean_object* v___x_4930_; 
if (v_isShared_4928_ == 0)
{
v___x_4930_ = v___x_4927_;
goto v_reusejp_4929_;
}
else
{
lean_object* v_reuseFailAlloc_4931_; 
v_reuseFailAlloc_4931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4931_, 0, v_a_4925_);
v___x_4930_ = v_reuseFailAlloc_4931_;
goto v_reusejp_4929_;
}
v_reusejp_4929_:
{
return v___x_4930_;
}
}
}
}
else
{
v_a_4880_ = v_b_4871_;
goto v___jp_4879_;
}
}
v___jp_4879_:
{
size_t v___x_4881_; size_t v___x_4882_; 
v___x_4881_ = ((size_t)1ULL);
v___x_4882_ = lean_usize_add(v_i_4870_, v___x_4881_);
v_i_4870_ = v___x_4882_;
v_b_4871_ = v_a_4880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v_a_4933_, lean_object* v___x_4934_, lean_object* v_as_4935_, lean_object* v_sz_4936_, lean_object* v_i_4937_, lean_object* v_b_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
size_t v_sz_boxed_4946_; size_t v_i_boxed_4947_; lean_object* v_res_4948_; 
v_sz_boxed_4946_ = lean_unbox_usize(v_sz_4936_);
lean_dec(v_sz_4936_);
v_i_boxed_4947_ = lean_unbox_usize(v_i_4937_);
lean_dec(v_i_4937_);
v_res_4948_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_a_4933_, v___x_4934_, v_as_4935_, v_sz_boxed_4946_, v_i_boxed_4947_, v_b_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v___y_4940_);
lean_dec_ref(v___y_4939_);
lean_dec_ref(v_as_4935_);
lean_dec_ref(v_a_4933_);
return v_res_4948_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2(void){
_start:
{
lean_object* v___x_4951_; lean_object* v___x_4952_; 
v___x_4951_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1));
v___x_4952_ = l_Lean_stringToMessageData(v___x_4951_);
return v___x_4952_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4(void){
_start:
{
lean_object* v___x_4954_; lean_object* v___x_4955_; 
v___x_4954_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3));
v___x_4955_ = l_Lean_stringToMessageData(v___x_4954_);
return v___x_4955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object* v_info_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
lean_object* v___y_4970_; lean_object* v___x_4973_; lean_object* v_frameDB_x3f_4974_; 
v___x_4973_ = lean_st_ref_get(v_a_4958_);
v_frameDB_x3f_4974_ = lean_ctor_get(v___x_4973_, 3);
lean_inc(v_frameDB_x3f_4974_);
lean_dec(v___x_4973_);
if (lean_obj_tag(v_frameDB_x3f_4974_) == 1)
{
lean_object* v_val_4975_; lean_object* v___f_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v_val_4975_ = lean_ctor_get(v_frameDB_x3f_4974_, 0);
lean_inc(v_val_4975_);
lean_dec_ref_known(v_frameDB_x3f_4974_, 1);
v___f_4976_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0));
v___x_4977_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_4956_);
v___x_4978_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v_val_4975_, v___f_4976_, v___x_4977_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
if (lean_obj_tag(v___x_4978_) == 0)
{
lean_object* v_a_4979_; lean_object* v_tree_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; size_t v_sz_4984_; size_t v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_5104_; 
v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
lean_inc(v_a_4979_);
lean_dec_ref_known(v___x_4978_, 1);
v_tree_4980_ = lean_ctor_get(v_a_4979_, 0);
v___x_4981_ = lean_box(0);
v___x_4982_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_4956_);
v___x_4983_ = l_Lean_Meta_Sym_getMatch___redArg(v_tree_4980_, v___x_4982_);
v_sz_4984_ = lean_array_size(v___x_4983_);
v___x_4985_ = ((size_t)0ULL);
lean_inc_ref(v___x_4982_);
v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_a_4979_, v___x_4982_, v___x_4983_, v_sz_4984_, v___x_4985_, v___x_4981_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec_ref(v___x_4983_);
v_isSharedCheck_5104_ = !lean_is_exclusive(v_a_4979_);
if (v_isSharedCheck_5104_ == 0)
{
lean_object* v_unused_5105_; lean_object* v_unused_5106_; 
v_unused_5105_ = lean_ctor_get(v_a_4979_, 1);
lean_dec(v_unused_5105_);
v_unused_5106_ = lean_ctor_get(v_a_4979_, 0);
lean_dec(v_unused_5106_);
v___x_4988_ = v_a_4979_;
v_isShared_4989_ = v_isSharedCheck_5104_;
goto v_resetjp_4987_;
}
else
{
lean_dec(v_a_4979_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_5104_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4990_; lean_object* v___x_4992_; uint8_t v_isShared_4993_; uint8_t v_isSharedCheck_5095_; 
v_a_4990_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_4992_ = v___x_4986_;
v_isShared_4993_ = v_isSharedCheck_5095_;
goto v_resetjp_4991_;
}
else
{
lean_inc(v_a_4990_);
lean_dec(v___x_4986_);
v___x_4992_ = lean_box(0);
v_isShared_4993_ = v_isSharedCheck_5095_;
goto v_resetjp_4991_;
}
v_resetjp_4991_:
{
if (lean_obj_tag(v_a_4990_) == 1)
{
lean_object* v_val_4994_; lean_object* v___x_4996_; uint8_t v_isShared_4997_; uint8_t v_isSharedCheck_5091_; 
lean_del_object(v___x_4992_);
v_val_4994_ = lean_ctor_get(v_a_4990_, 0);
v_isSharedCheck_5091_ = !lean_is_exclusive(v_a_4990_);
if (v_isSharedCheck_5091_ == 0)
{
v___x_4996_ = v_a_4990_;
v_isShared_4997_ = v_isSharedCheck_5091_;
goto v_resetjp_4995_;
}
else
{
lean_inc(v_val_4994_);
lean_dec(v_a_4990_);
v___x_4996_ = lean_box(0);
v_isShared_4997_ = v_isSharedCheck_5091_;
goto v_resetjp_4995_;
}
v_resetjp_4995_:
{
lean_object* v_fst_4998_; lean_object* v_snd_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5090_; 
v_fst_4998_ = lean_ctor_get(v_val_4994_, 0);
v_snd_4999_ = lean_ctor_get(v_val_4994_, 1);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_val_4994_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5001_ = v_val_4994_;
v_isShared_5002_ = v_isSharedCheck_5090_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_snd_4999_);
lean_inc(v_fst_4998_);
lean_dec(v_val_4994_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5090_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5003_; lean_object* v_specBackwardRuleCache_5004_; lean_object* v_splitBackwardRuleCache_5005_; lean_object* v_latticeBackwardRuleCache_5006_; lean_object* v_frameDB_x3f_5007_; lean_object* v_invariants_5008_; lean_object* v_vcs_5009_; lean_object* v_simpState_5010_; lean_object* v_fuel_5011_; lean_object* v_inlineHandledInvariants_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5089_; 
v___x_5003_ = lean_st_ref_take(v_a_4958_);
v_specBackwardRuleCache_5004_ = lean_ctor_get(v___x_5003_, 0);
v_splitBackwardRuleCache_5005_ = lean_ctor_get(v___x_5003_, 1);
v_latticeBackwardRuleCache_5006_ = lean_ctor_get(v___x_5003_, 2);
v_frameDB_x3f_5007_ = lean_ctor_get(v___x_5003_, 3);
v_invariants_5008_ = lean_ctor_get(v___x_5003_, 4);
v_vcs_5009_ = lean_ctor_get(v___x_5003_, 5);
v_simpState_5010_ = lean_ctor_get(v___x_5003_, 6);
v_fuel_5011_ = lean_ctor_get(v___x_5003_, 7);
v_inlineHandledInvariants_5012_ = lean_ctor_get(v___x_5003_, 8);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5014_ = v___x_5003_;
v_isShared_5015_ = v_isSharedCheck_5089_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_inlineHandledInvariants_5012_);
lean_inc(v_fuel_5011_);
lean_inc(v_simpState_5010_);
lean_inc(v_vcs_5009_);
lean_inc(v_invariants_5008_);
lean_inc(v_frameDB_x3f_5007_);
lean_inc(v_latticeBackwardRuleCache_5006_);
lean_inc(v_splitBackwardRuleCache_5005_);
lean_inc(v_specBackwardRuleCache_5004_);
lean_dec(v___x_5003_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5089_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___y_5017_; lean_object* v___y_5060_; 
if (lean_obj_tag(v_frameDB_x3f_5007_) == 0)
{
lean_del_object(v___x_4996_);
v___y_5017_ = v_frameDB_x3f_5007_;
goto v___jp_5016_;
}
else
{
lean_object* v_val_5064_; 
v_val_5064_ = lean_ctor_get(v_frameDB_x3f_5007_, 0);
lean_inc(v_val_5064_);
lean_dec_ref_known(v_frameDB_x3f_5007_, 1);
if (lean_obj_tag(v_val_5064_) == 1)
{
lean_object* v_value_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5088_; 
v_value_5065_ = lean_ctor_get(v_val_5064_, 0);
v_isSharedCheck_5088_ = !lean_is_exclusive(v_val_5064_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5067_ = v_val_5064_;
v_isShared_5068_ = v_isSharedCheck_5088_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_value_5065_);
lean_dec(v_val_5064_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5088_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v_tree_5069_; lean_object* v_entries_5070_; lean_object* v___x_5072_; uint8_t v_isShared_5073_; uint8_t v_isSharedCheck_5087_; 
v_tree_5069_ = lean_ctor_get(v_value_5065_, 0);
v_entries_5070_ = lean_ctor_get(v_value_5065_, 1);
v_isSharedCheck_5087_ = !lean_is_exclusive(v_value_5065_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5072_ = v_value_5065_;
v_isShared_5073_ = v_isSharedCheck_5087_;
goto v_resetjp_5071_;
}
else
{
lean_inc(v_entries_5070_);
lean_inc(v_tree_5069_);
lean_dec(v_value_5065_);
v___x_5072_ = lean_box(0);
v_isShared_5073_ = v_isSharedCheck_5087_;
goto v_resetjp_5071_;
}
v_resetjp_5071_:
{
lean_object* v_pat_5074_; lean_object* v_varNames_5075_; lean_object* v_frameStx_5076_; lean_object* v_srcIdx_5077_; uint8_t v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
v_pat_5074_ = lean_ctor_get(v_fst_4998_, 0);
v_varNames_5075_ = lean_ctor_get(v_fst_4998_, 1);
v_frameStx_5076_ = lean_ctor_get(v_fst_4998_, 2);
v_srcIdx_5077_ = lean_ctor_get(v_fst_4998_, 3);
v___x_5078_ = 1;
lean_inc(v_srcIdx_5077_);
lean_inc(v_frameStx_5076_);
lean_inc_ref(v_varNames_5075_);
lean_inc_ref(v_pat_5074_);
v___x_5079_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5079_, 0, v_pat_5074_);
lean_ctor_set(v___x_5079_, 1, v_varNames_5075_);
lean_ctor_set(v___x_5079_, 2, v_frameStx_5076_);
lean_ctor_set(v___x_5079_, 3, v_srcIdx_5077_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*4, v___x_5078_);
v___x_5080_ = lean_array_set(v_entries_5070_, v_srcIdx_5077_, v___x_5079_);
if (v_isShared_5073_ == 0)
{
lean_ctor_set(v___x_5072_, 1, v___x_5080_);
v___x_5082_ = v___x_5072_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_tree_5069_);
lean_ctor_set(v_reuseFailAlloc_5086_, 1, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
lean_object* v___x_5084_; 
if (v_isShared_5068_ == 0)
{
lean_ctor_set(v___x_5067_, 0, v___x_5082_);
v___x_5084_ = v___x_5067_;
goto v_reusejp_5083_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5082_);
v___x_5084_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5083_;
}
v_reusejp_5083_:
{
v___y_5060_ = v___x_5084_;
goto v___jp_5059_;
}
}
}
}
}
else
{
v___y_5060_ = v_val_5064_;
goto v___jp_5059_;
}
}
v___jp_5016_:
{
lean_object* v___x_5019_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 3, v___y_5017_);
v___x_5019_ = v___x_5014_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_specBackwardRuleCache_5004_);
lean_ctor_set(v_reuseFailAlloc_5058_, 1, v_splitBackwardRuleCache_5005_);
lean_ctor_set(v_reuseFailAlloc_5058_, 2, v_latticeBackwardRuleCache_5006_);
lean_ctor_set(v_reuseFailAlloc_5058_, 3, v___y_5017_);
lean_ctor_set(v_reuseFailAlloc_5058_, 4, v_invariants_5008_);
lean_ctor_set(v_reuseFailAlloc_5058_, 5, v_vcs_5009_);
lean_ctor_set(v_reuseFailAlloc_5058_, 6, v_simpState_5010_);
lean_ctor_set(v_reuseFailAlloc_5058_, 7, v_fuel_5011_);
lean_ctor_set(v_reuseFailAlloc_5058_, 8, v_inlineHandledInvariants_5012_);
v___x_5019_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_st_ref_set(v_a_4958_, v___x_5019_);
v___x_5021_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_fst_4998_, v_snd_4999_, v_info_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
lean_dec(v_snd_4999_);
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_options_5022_; uint8_t v_hasTrace_5023_; 
v_options_5022_ = lean_ctor_get(v_a_4966_, 2);
v_hasTrace_5023_ = lean_ctor_get_uint8(v_options_5022_, sizeof(void*)*1);
if (v_hasTrace_5023_ == 0)
{
lean_object* v_a_5024_; 
lean_del_object(v___x_5001_);
lean_del_object(v___x_4988_);
lean_dec_ref(v___x_4982_);
v_a_5024_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___x_5021_, 1);
v___y_4970_ = v_a_5024_;
goto v___jp_4969_;
}
else
{
lean_object* v_a_5025_; lean_object* v_inheritedTraceOptions_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; uint8_t v___x_5029_; 
v_a_5025_ = lean_ctor_get(v___x_5021_, 0);
lean_inc(v_a_5025_);
lean_dec_ref_known(v___x_5021_, 1);
v_inheritedTraceOptions_5026_ = lean_ctor_get(v_a_4966_, 13);
v___x_5027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_5028_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5029_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5026_, v_options_5022_, v___x_5028_);
if (v___x_5029_ == 0)
{
lean_del_object(v___x_5001_);
lean_del_object(v___x_4988_);
lean_dec_ref(v___x_4982_);
v___y_4970_ = v_a_5025_;
goto v___jp_4969_;
}
else
{
lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5033_; 
v___x_5030_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2);
v___x_5031_ = l_Lean_MessageData_ofExpr(v___x_4982_);
if (v_isShared_5002_ == 0)
{
lean_ctor_set_tag(v___x_5001_, 7);
lean_ctor_set(v___x_5001_, 1, v___x_5031_);
lean_ctor_set(v___x_5001_, 0, v___x_5030_);
v___x_5033_ = v___x_5001_;
goto v_reusejp_5032_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v___x_5030_);
lean_ctor_set(v_reuseFailAlloc_5049_, 1, v___x_5031_);
v___x_5033_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5032_;
}
v_reusejp_5032_:
{
lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5034_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4);
if (v_isShared_4989_ == 0)
{
lean_ctor_set_tag(v___x_4988_, 7);
lean_ctor_set(v___x_4988_, 1, v___x_5034_);
lean_ctor_set(v___x_4988_, 0, v___x_5033_);
v___x_5036_ = v___x_4988_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v___x_5033_);
lean_ctor_set(v_reuseFailAlloc_5048_, 1, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
lean_inc(v_a_5025_);
v___x_5037_ = l_Lean_indentExpr(v_a_5025_);
v___x_5038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5038_, 0, v___x_5036_);
lean_ctor_set(v___x_5038_, 1, v___x_5037_);
v___x_5039_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5027_, v___x_5038_, v_a_4964_, v_a_4965_, v_a_4966_, v_a_4967_);
if (lean_obj_tag(v___x_5039_) == 0)
{
lean_dec_ref_known(v___x_5039_, 1);
v___y_4970_ = v_a_5025_;
goto v___jp_4969_;
}
else
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
lean_dec(v_a_5025_);
v_a_5040_ = lean_ctor_get(v___x_5039_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v___x_5039_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v___x_5039_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v___x_5039_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
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
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
lean_del_object(v___x_5001_);
lean_del_object(v___x_4988_);
lean_dec_ref(v___x_4982_);
v_a_5050_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5021_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5021_);
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
v___jp_5059_:
{
lean_object* v___x_5062_; 
if (v_isShared_4997_ == 0)
{
lean_ctor_set(v___x_4996_, 0, v___y_5060_);
v___x_5062_ = v___x_4996_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___y_5060_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
v___y_5017_ = v___x_5062_;
goto v___jp_5016_;
}
}
}
}
}
}
else
{
lean_object* v___x_5093_; 
lean_dec(v_a_4990_);
lean_del_object(v___x_4988_);
lean_dec_ref(v___x_4982_);
lean_dec_ref(v_info_4956_);
if (v_isShared_4993_ == 0)
{
lean_ctor_set(v___x_4992_, 0, v___x_4981_);
v___x_5093_ = v___x_4992_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v___x_4981_);
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
lean_del_object(v___x_4988_);
lean_dec_ref(v___x_4982_);
lean_dec_ref(v_info_4956_);
v_a_5096_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_4986_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_4986_);
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
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec_ref(v_info_4956_);
v_a_5107_ = lean_ctor_get(v___x_4978_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_4978_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_4978_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_4978_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
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
lean_object* v___x_5115_; lean_object* v___x_5116_; 
lean_dec(v_frameDB_x3f_4974_);
lean_dec_ref(v_info_4956_);
v___x_5115_ = lean_box(0);
v___x_5116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5116_, 0, v___x_5115_);
return v___x_5116_;
}
v___jp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4971_, 0, v___y_4970_);
v___x_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4971_);
return v___x_4972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object* v_info_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_, lean_object* v_a_5124_, lean_object* v_a_5125_, lean_object* v_a_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_){
_start:
{
lean_object* v_res_5130_; 
v_res_5130_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_info_5117_, v_a_5118_, v_a_5119_, v_a_5120_, v_a_5121_, v_a_5122_, v_a_5123_, v_a_5124_, v_a_5125_, v_a_5126_, v_a_5127_, v_a_5128_);
lean_dec(v_a_5128_);
lean_dec_ref(v_a_5127_);
lean_dec(v_a_5126_);
lean_dec_ref(v_a_5125_);
lean_dec(v_a_5124_);
lean_dec_ref(v_a_5123_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_a_5120_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
return v_res_5130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object* v_a_5131_, lean_object* v___x_5132_, lean_object* v_as_5133_, size_t v_sz_5134_, size_t v_i_5135_, lean_object* v_b_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_, lean_object* v___y_5141_, lean_object* v___y_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v___x_5149_; 
v___x_5149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_a_5131_, v___x_5132_, v_as_5133_, v_sz_5134_, v_i_5135_, v_b_5136_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_, v___y_5147_);
return v___x_5149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_a_5150_ = _args[0];
lean_object* v___x_5151_ = _args[1];
lean_object* v_as_5152_ = _args[2];
lean_object* v_sz_5153_ = _args[3];
lean_object* v_i_5154_ = _args[4];
lean_object* v_b_5155_ = _args[5];
lean_object* v___y_5156_ = _args[6];
lean_object* v___y_5157_ = _args[7];
lean_object* v___y_5158_ = _args[8];
lean_object* v___y_5159_ = _args[9];
lean_object* v___y_5160_ = _args[10];
lean_object* v___y_5161_ = _args[11];
lean_object* v___y_5162_ = _args[12];
lean_object* v___y_5163_ = _args[13];
lean_object* v___y_5164_ = _args[14];
lean_object* v___y_5165_ = _args[15];
lean_object* v___y_5166_ = _args[16];
lean_object* v___y_5167_ = _args[17];
_start:
{
size_t v_sz_boxed_5168_; size_t v_i_boxed_5169_; lean_object* v_res_5170_; 
v_sz_boxed_5168_ = lean_unbox_usize(v_sz_5153_);
lean_dec(v_sz_5153_);
v_i_boxed_5169_ = lean_unbox_usize(v_i_5154_);
lean_dec(v_i_5154_);
v_res_5170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(v_a_5150_, v___x_5151_, v_as_5152_, v_sz_boxed_5168_, v_i_boxed_5169_, v_b_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_, v___y_5164_, v___y_5165_, v___y_5166_);
lean_dec(v___y_5166_);
lean_dec_ref(v___y_5165_);
lean_dec(v___y_5164_);
lean_dec_ref(v___y_5163_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
lean_dec(v___y_5157_);
lean_dec_ref(v___y_5156_);
lean_dec_ref(v_as_5152_);
lean_dec_ref(v_a_5150_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx(lean_object* v_x_5171_){
_start:
{
if (lean_obj_tag(v_x_5171_) == 0)
{
lean_object* v___x_5172_; 
v___x_5172_ = lean_unsigned_to_nat(0u);
return v___x_5172_;
}
else
{
lean_object* v___x_5173_; 
v___x_5173_ = lean_unsigned_to_nat(1u);
return v___x_5173_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx___boxed(lean_object* v_x_5174_){
_start:
{
lean_object* v_res_5175_; 
v_res_5175_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx(v_x_5174_);
lean_dec_ref(v_x_5174_);
return v_res_5175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(lean_object* v_t_5176_, lean_object* v_k_5177_){
_start:
{
if (lean_obj_tag(v_t_5176_) == 0)
{
lean_object* v_scope_5178_; lean_object* v_subgoals_5179_; lean_object* v___x_5180_; 
v_scope_5178_ = lean_ctor_get(v_t_5176_, 0);
lean_inc_ref(v_scope_5178_);
v_subgoals_5179_ = lean_ctor_get(v_t_5176_, 1);
lean_inc(v_subgoals_5179_);
lean_dec_ref_known(v_t_5176_, 2);
v___x_5180_ = lean_apply_2(v_k_5177_, v_scope_5178_, v_subgoals_5179_);
return v___x_5180_;
}
else
{
lean_object* v_goal_5181_; lean_object* v_info_5182_; lean_object* v___x_5183_; 
v_goal_5181_ = lean_ctor_get(v_t_5176_, 0);
lean_inc(v_goal_5181_);
v_info_5182_ = lean_ctor_get(v_t_5176_, 1);
lean_inc_ref(v_info_5182_);
lean_dec_ref_known(v_t_5176_, 2);
v___x_5183_ = lean_apply_2(v_k_5177_, v_goal_5181_, v_info_5182_);
return v___x_5183_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim(lean_object* v_motive_5184_, lean_object* v_ctorIdx_5185_, lean_object* v_t_5186_, lean_object* v_h_5187_, lean_object* v_k_5188_){
_start:
{
lean_object* v___x_5189_; 
v___x_5189_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5186_, v_k_5188_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___boxed(lean_object* v_motive_5190_, lean_object* v_ctorIdx_5191_, lean_object* v_t_5192_, lean_object* v_h_5193_, lean_object* v_k_5194_){
_start:
{
lean_object* v_res_5195_; 
v_res_5195_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim(v_motive_5190_, v_ctorIdx_5191_, v_t_5192_, v_h_5193_, v_k_5194_);
lean_dec(v_ctorIdx_5191_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_framed_elim___redArg(lean_object* v_t_5196_, lean_object* v_framed_5197_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5196_, v_framed_5197_);
return v___x_5198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_framed_elim(lean_object* v_motive_5199_, lean_object* v_t_5200_, lean_object* v_h_5201_, lean_object* v_framed_5202_){
_start:
{
lean_object* v___x_5203_; 
v___x_5203_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5200_, v_framed_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_notFramed_elim___redArg(lean_object* v_t_5204_, lean_object* v_notFramed_5205_){
_start:
{
lean_object* v___x_5206_; 
v___x_5206_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5204_, v_notFramed_5205_);
return v___x_5206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_notFramed_elim(lean_object* v_motive_5207_, lean_object* v_t_5208_, lean_object* v_h_5209_, lean_object* v_notFramed_5210_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5208_, v_notFramed_5210_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(size_t v_sz_5212_, size_t v_i_5213_, lean_object* v_bs_5214_){
_start:
{
uint8_t v___x_5215_; 
v___x_5215_ = lean_usize_dec_lt(v_i_5213_, v_sz_5212_);
if (v___x_5215_ == 0)
{
return v_bs_5214_;
}
else
{
lean_object* v_v_5216_; lean_object* v___x_5217_; lean_object* v_bs_x27_5218_; lean_object* v___x_5219_; size_t v___x_5220_; size_t v___x_5221_; lean_object* v___x_5222_; 
v_v_5216_ = lean_array_uget(v_bs_5214_, v_i_5213_);
v___x_5217_ = lean_unsigned_to_nat(0u);
v_bs_x27_5218_ = lean_array_uset(v_bs_5214_, v_i_5213_, v___x_5217_);
v___x_5219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5219_, 0, v_v_5216_);
v___x_5220_ = ((size_t)1ULL);
v___x_5221_ = lean_usize_add(v_i_5213_, v___x_5220_);
v___x_5222_ = lean_array_uset(v_bs_x27_5218_, v_i_5213_, v___x_5219_);
v_i_5213_ = v___x_5221_;
v_bs_5214_ = v___x_5222_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0___boxed(lean_object* v_sz_5224_, lean_object* v_i_5225_, lean_object* v_bs_5226_){
_start:
{
size_t v_sz_boxed_5227_; size_t v_i_boxed_5228_; lean_object* v_res_5229_; 
v_sz_boxed_5227_ = lean_unbox_usize(v_sz_5224_);
lean_dec(v_sz_5224_);
v_i_boxed_5228_ = lean_unbox_usize(v_i_5225_);
lean_dec(v_i_5225_);
v_res_5229_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(v_sz_boxed_5227_, v_i_boxed_5228_, v_bs_5226_);
return v_res_5229_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; 
v___x_5231_ = lean_box(0);
v___x_5232_ = lean_unsigned_to_nat(2u);
v___x_5233_ = lean_mk_empty_array_with_capacity(v___x_5232_);
v___x_5234_ = lean_array_push(v___x_5233_, v___x_5231_);
return v___x_5234_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5236_; lean_object* v___x_5237_; 
v___x_5236_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__2));
v___x_5237_ = l_Lean_stringToMessageData(v___x_5236_);
return v___x_5237_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5239_; lean_object* v___x_5240_; 
v___x_5239_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__4));
v___x_5240_ = l_Lean_stringToMessageData(v___x_5239_);
return v___x_5240_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5242_; lean_object* v___x_5243_; 
v___x_5242_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__6));
v___x_5243_ = l_Lean_stringToMessageData(v___x_5242_);
return v___x_5243_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5245_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__8));
v___x_5246_ = l_Lean_stringToMessageData(v___x_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0(uint8_t v___x_5247_, lean_object* v_info_5248_, lean_object* v___x_5249_, lean_object* v___x_5250_, lean_object* v___x_5251_, lean_object* v___x_5252_, lean_object* v___x_5253_, lean_object* v_goal_5254_, lean_object* v_scope_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_, lean_object* v___y_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_){
_start:
{
if (v___x_5247_ == 0)
{
lean_object* v___x_5268_; 
lean_inc_ref(v_info_5248_);
v___x_5268_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_info_5248_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5364_; 
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5271_ = v___x_5268_;
v_isShared_5272_ = v_isSharedCheck_5364_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5268_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5364_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
if (lean_obj_tag(v_a_5269_) == 1)
{
lean_object* v_args_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; size_t v_sz_5279_; size_t v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; 
lean_del_object(v___x_5271_);
v_args_5273_ = lean_ctor_get(v_info_5248_, 1);
v___x_5274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__0));
v___x_5275_ = l_Lean_Name_mkStr5(v___x_5249_, v___x_5250_, v___x_5251_, v___x_5252_, v___x_5274_);
v___x_5276_ = lean_unsigned_to_nat(7u);
v___x_5277_ = lean_unsigned_to_nat(0u);
v___x_5278_ = l_Array_extract___redArg(v_args_5273_, v___x_5277_, v___x_5276_);
v_sz_5279_ = lean_array_size(v___x_5278_);
v___x_5280_ = ((size_t)0ULL);
v___x_5281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(v_sz_5279_, v___x_5280_, v___x_5278_);
v___x_5282_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1);
v___x_5283_ = lean_array_push(v___x_5282_, v_a_5269_);
v___x_5284_ = l_Array_append___redArg(v___x_5281_, v___x_5283_);
lean_dec_ref(v___x_5283_);
v___x_5285_ = l_Lean_Meta_mkAppOptM(v___x_5275_, v___x_5284_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5285_) == 0)
{
lean_object* v_a_5286_; lean_object* v_ref_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; 
v_a_5286_ = lean_ctor_get(v___x_5285_, 0);
lean_inc(v_a_5286_);
lean_dec_ref_known(v___x_5285_, 1);
v_ref_5287_ = lean_ctor_get(v___y_5265_, 5);
v___x_5288_ = lean_unsigned_to_nat(1000u);
lean_inc(v_ref_5287_);
v___x_5289_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx(v_ref_5287_, v_a_5286_, v___x_5288_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5289_) == 0)
{
lean_object* v_a_5290_; 
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
lean_inc(v_a_5290_);
lean_dec_ref_known(v___x_5289_, 1);
if (lean_obj_tag(v_a_5290_) == 1)
{
lean_object* v_val_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v_val_5291_ = lean_ctor_get(v_a_5290_, 0);
lean_inc(v_val_5291_);
lean_dec_ref_known(v_a_5290_, 1);
v___x_5292_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_5293_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(v_val_5291_, v_info_5248_, v___x_5292_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
lean_dec_ref(v_info_5248_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
lean_inc(v_a_5294_);
lean_dec_ref_known(v___x_5293_, 1);
if (lean_obj_tag(v_a_5294_) == 1)
{
lean_object* v_val_5295_; lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5327_; 
v_val_5295_ = lean_ctor_get(v_a_5294_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v_a_5294_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5297_ = v_a_5294_;
v_isShared_5298_ = v_isSharedCheck_5327_;
goto v_resetjp_5296_;
}
else
{
lean_inc(v_val_5295_);
lean_dec(v_a_5294_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5327_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5299_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3);
v___x_5300_ = l_Lean_indentExpr(v___x_5253_);
lean_inc_ref(v___x_5300_);
v___x_5301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5301_, 0, v___x_5299_);
lean_ctor_set(v___x_5301_, 1, v___x_5300_);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5301_);
v___x_5303_ = v___x_5297_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5304_; 
v___x_5304_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_5295_, v_goal_5254_, v___x_5303_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5317_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5317_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5317_ == 0)
{
v___x_5307_ = v___x_5304_;
v_isShared_5308_ = v_isSharedCheck_5317_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5304_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5317_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
if (lean_obj_tag(v_a_5305_) == 1)
{
lean_object* v_mvarIds_5309_; lean_object* v___x_5310_; lean_object* v___x_5312_; 
lean_dec_ref(v___x_5300_);
v_mvarIds_5309_ = lean_ctor_get(v_a_5305_, 0);
lean_inc(v_mvarIds_5309_);
lean_dec_ref_known(v_a_5305_, 1);
v___x_5310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5310_, 0, v_scope_5255_);
lean_ctor_set(v___x_5310_, 1, v_mvarIds_5309_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 0, v___x_5310_);
v___x_5312_ = v___x_5307_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v___x_5310_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
else
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; 
lean_del_object(v___x_5307_);
lean_dec(v_a_5305_);
lean_dec_ref(v_scope_5255_);
v___x_5314_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5);
v___x_5315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5314_);
lean_ctor_set(v___x_5315_, 1, v___x_5300_);
v___x_5316_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5315_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
return v___x_5316_;
}
}
}
else
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
lean_dec_ref(v___x_5300_);
lean_dec_ref(v_scope_5255_);
v_a_5318_ = lean_ctor_get(v___x_5304_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5304_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5304_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5304_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
}
}
}
}
else
{
lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; 
lean_dec(v_a_5294_);
lean_dec_ref(v_scope_5255_);
lean_dec(v_goal_5254_);
v___x_5328_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7);
v___x_5329_ = l_Lean_indentExpr(v___x_5253_);
v___x_5330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5330_, 0, v___x_5328_);
lean_ctor_set(v___x_5330_, 1, v___x_5329_);
v___x_5331_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5330_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
return v___x_5331_;
}
}
else
{
lean_object* v_a_5332_; lean_object* v___x_5334_; uint8_t v_isShared_5335_; uint8_t v_isSharedCheck_5339_; 
lean_dec_ref(v_scope_5255_);
lean_dec(v_goal_5254_);
lean_dec_ref(v___x_5253_);
v_a_5332_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5339_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5339_ == 0)
{
v___x_5334_ = v___x_5293_;
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
else
{
lean_inc(v_a_5332_);
lean_dec(v___x_5293_);
v___x_5334_ = lean_box(0);
v_isShared_5335_ = v_isSharedCheck_5339_;
goto v_resetjp_5333_;
}
v_resetjp_5333_:
{
lean_object* v___x_5337_; 
if (v_isShared_5335_ == 0)
{
v___x_5337_ = v___x_5334_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v_a_5332_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
}
}
else
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; 
lean_dec(v_a_5290_);
lean_dec_ref(v_scope_5255_);
lean_dec(v_goal_5254_);
lean_dec_ref(v_info_5248_);
v___x_5340_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9);
v___x_5341_ = l_Lean_indentExpr(v___x_5253_);
v___x_5342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5342_, 0, v___x_5340_);
lean_ctor_set(v___x_5342_, 1, v___x_5341_);
v___x_5343_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5342_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
return v___x_5343_;
}
}
else
{
lean_object* v_a_5344_; lean_object* v___x_5346_; uint8_t v_isShared_5347_; uint8_t v_isSharedCheck_5351_; 
lean_dec_ref(v_scope_5255_);
lean_dec(v_goal_5254_);
lean_dec_ref(v___x_5253_);
lean_dec_ref(v_info_5248_);
v_a_5344_ = lean_ctor_get(v___x_5289_, 0);
v_isSharedCheck_5351_ = !lean_is_exclusive(v___x_5289_);
if (v_isSharedCheck_5351_ == 0)
{
v___x_5346_ = v___x_5289_;
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
else
{
lean_inc(v_a_5344_);
lean_dec(v___x_5289_);
v___x_5346_ = lean_box(0);
v_isShared_5347_ = v_isSharedCheck_5351_;
goto v_resetjp_5345_;
}
v_resetjp_5345_:
{
lean_object* v___x_5349_; 
if (v_isShared_5347_ == 0)
{
v___x_5349_ = v___x_5346_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5350_; 
v_reuseFailAlloc_5350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5350_, 0, v_a_5344_);
v___x_5349_ = v_reuseFailAlloc_5350_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
return v___x_5349_;
}
}
}
}
else
{
lean_object* v_a_5352_; lean_object* v___x_5354_; uint8_t v_isShared_5355_; uint8_t v_isSharedCheck_5359_; 
lean_dec_ref(v_scope_5255_);
lean_dec(v_goal_5254_);
lean_dec_ref(v___x_5253_);
lean_dec_ref(v_info_5248_);
v_a_5352_ = lean_ctor_get(v___x_5285_, 0);
v_isSharedCheck_5359_ = !lean_is_exclusive(v___x_5285_);
if (v_isSharedCheck_5359_ == 0)
{
v___x_5354_ = v___x_5285_;
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
else
{
lean_inc(v_a_5352_);
lean_dec(v___x_5285_);
v___x_5354_ = lean_box(0);
v_isShared_5355_ = v_isSharedCheck_5359_;
goto v_resetjp_5353_;
}
v_resetjp_5353_:
{
lean_object* v___x_5357_; 
if (v_isShared_5355_ == 0)
{
v___x_5357_ = v___x_5354_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5358_; 
v_reuseFailAlloc_5358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5358_, 0, v_a_5352_);
v___x_5357_ = v_reuseFailAlloc_5358_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
return v___x_5357_;
}
}
}
}
else
{
lean_object* v___x_5360_; lean_object* v___x_5362_; 
lean_dec(v_a_5269_);
lean_dec_ref(v_scope_5255_);
lean_dec_ref(v___x_5253_);
lean_dec_ref(v___x_5252_);
lean_dec_ref(v___x_5251_);
lean_dec_ref(v___x_5250_);
lean_dec_ref(v___x_5249_);
v___x_5360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5360_, 0, v_goal_5254_);
lean_ctor_set(v___x_5360_, 1, v_info_5248_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 0, v___x_5360_);
v___x_5362_ = v___x_5271_;
goto v_reusejp_5361_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5360_);
v___x_5362_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5361_;
}
v_reusejp_5361_:
{
return v___x_5362_;
}
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec_ref(v_scope_5255_);
lean_dec(v_goal_5254_);
lean_dec_ref(v___x_5253_);
lean_dec_ref(v___x_5252_);
lean_dec_ref(v___x_5251_);
lean_dec_ref(v___x_5250_);
lean_dec_ref(v___x_5249_);
lean_dec_ref(v_info_5248_);
v_a_5365_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5268_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5268_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
else
{
lean_object* v_strippedProg_5373_; lean_object* v___x_5374_; 
lean_dec_ref(v_scope_5255_);
lean_dec_ref(v___x_5252_);
lean_dec_ref(v___x_5251_);
lean_dec_ref(v___x_5250_);
lean_dec_ref(v___x_5249_);
v_strippedProg_5373_ = l_Lean_Expr_appArg_x21(v___x_5253_);
lean_dec_ref(v___x_5253_);
lean_inc_ref(v_strippedProg_5373_);
lean_inc_ref(v_info_5248_);
v___x_5374_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5254_, v_info_5248_, v_strippedProg_5373_, v___y_5256_, v___y_5257_, v___y_5258_, v___y_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5395_; 
v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5395_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5377_ = v___x_5374_;
v_isShared_5378_ = v_isSharedCheck_5395_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5374_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5395_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v_head_5379_; lean_object* v_args_5380_; lean_object* v_excessArgs_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5394_; 
v_head_5379_ = lean_ctor_get(v_info_5248_, 0);
v_args_5380_ = lean_ctor_get(v_info_5248_, 1);
v_excessArgs_5381_ = lean_ctor_get(v_info_5248_, 2);
v_isSharedCheck_5394_ = !lean_is_exclusive(v_info_5248_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5383_ = v_info_5248_;
v_isShared_5384_ = v_isSharedCheck_5394_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_excessArgs_5381_);
lean_inc(v_args_5380_);
lean_inc(v_head_5379_);
lean_dec(v_info_5248_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5394_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
lean_object* v___x_5385_; lean_object* v___x_5386_; lean_object* v___x_5388_; 
v___x_5385_ = lean_unsigned_to_nat(7u);
v___x_5386_ = lean_array_set(v_args_5380_, v___x_5385_, v_strippedProg_5373_);
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 1, v___x_5386_);
v___x_5388_ = v___x_5383_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_head_5379_);
lean_ctor_set(v_reuseFailAlloc_5393_, 1, v___x_5386_);
lean_ctor_set(v_reuseFailAlloc_5393_, 2, v_excessArgs_5381_);
v___x_5388_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
lean_object* v___x_5389_; lean_object* v___x_5391_; 
v___x_5389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5389_, 0, v_a_5375_);
lean_ctor_set(v___x_5389_, 1, v___x_5388_);
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 0, v___x_5389_);
v___x_5391_ = v___x_5377_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5389_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
}
else
{
lean_object* v_a_5396_; lean_object* v___x_5398_; uint8_t v_isShared_5399_; uint8_t v_isSharedCheck_5403_; 
lean_dec_ref(v_strippedProg_5373_);
lean_dec_ref(v_info_5248_);
v_a_5396_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5398_ = v___x_5374_;
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
else
{
lean_inc(v_a_5396_);
lean_dec(v___x_5374_);
v___x_5398_ = lean_box(0);
v_isShared_5399_ = v_isSharedCheck_5403_;
goto v_resetjp_5397_;
}
v_resetjp_5397_:
{
lean_object* v___x_5401_; 
if (v_isShared_5399_ == 0)
{
v___x_5401_ = v___x_5398_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5402_, 0, v_a_5396_);
v___x_5401_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
return v___x_5401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___boxed(lean_object** _args){
lean_object* v___x_5404_ = _args[0];
lean_object* v_info_5405_ = _args[1];
lean_object* v___x_5406_ = _args[2];
lean_object* v___x_5407_ = _args[3];
lean_object* v___x_5408_ = _args[4];
lean_object* v___x_5409_ = _args[5];
lean_object* v___x_5410_ = _args[6];
lean_object* v_goal_5411_ = _args[7];
lean_object* v_scope_5412_ = _args[8];
lean_object* v___y_5413_ = _args[9];
lean_object* v___y_5414_ = _args[10];
lean_object* v___y_5415_ = _args[11];
lean_object* v___y_5416_ = _args[12];
lean_object* v___y_5417_ = _args[13];
lean_object* v___y_5418_ = _args[14];
lean_object* v___y_5419_ = _args[15];
lean_object* v___y_5420_ = _args[16];
lean_object* v___y_5421_ = _args[17];
lean_object* v___y_5422_ = _args[18];
lean_object* v___y_5423_ = _args[19];
lean_object* v___y_5424_ = _args[20];
_start:
{
uint8_t v___x_25457__boxed_5425_; lean_object* v_res_5426_; 
v___x_25457__boxed_5425_ = lean_unbox(v___x_5404_);
v_res_5426_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0(v___x_25457__boxed_5425_, v_info_5405_, v___x_5406_, v___x_5407_, v___x_5408_, v___x_5409_, v___x_5410_, v_goal_5411_, v_scope_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_);
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5422_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec(v___y_5415_);
lean_dec(v___y_5414_);
lean_dec_ref(v___y_5413_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(lean_object* v_scope_5435_, lean_object* v_goal_5436_, lean_object* v_info_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_){
_start:
{
lean_object* v___x_5450_; lean_object* v___x_5451_; lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; lean_object* v___x_5458_; lean_object* v___y_5459_; lean_object* v___x_5460_; 
v___x_5450_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_5437_);
v___x_5451_ = l_Lean_Expr_getAppFn(v___x_5450_);
v___x_5452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0));
v___x_5453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1));
v___x_5454_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2));
v___x_5455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__0));
v___x_5456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2));
v___x_5457_ = l_Lean_Expr_isConstOf(v___x_5451_, v___x_5456_);
lean_dec_ref(v___x_5451_);
v___x_5458_ = lean_box(v___x_5457_);
lean_inc(v_goal_5436_);
v___y_5459_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___boxed), 21, 9);
lean_closure_set(v___y_5459_, 0, v___x_5458_);
lean_closure_set(v___y_5459_, 1, v_info_5437_);
lean_closure_set(v___y_5459_, 2, v___x_5452_);
lean_closure_set(v___y_5459_, 3, v___x_5453_);
lean_closure_set(v___y_5459_, 4, v___x_5454_);
lean_closure_set(v___y_5459_, 5, v___x_5455_);
lean_closure_set(v___y_5459_, 6, v___x_5450_);
lean_closure_set(v___y_5459_, 7, v_goal_5436_);
lean_closure_set(v___y_5459_, 8, v_scope_5435_);
v___x_5460_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5436_, v___y_5459_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
return v___x_5460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___boxed(lean_object* v_scope_5461_, lean_object* v_goal_5462_, lean_object* v_info_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_, lean_object* v_a_5468_, lean_object* v_a_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_){
_start:
{
lean_object* v_res_5476_; 
v_res_5476_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(v_scope_5461_, v_goal_5462_, v_info_5463_, v_a_5464_, v_a_5465_, v_a_5466_, v_a_5467_, v_a_5468_, v_a_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_);
lean_dec(v_a_5474_);
lean_dec_ref(v_a_5473_);
lean_dec(v_a_5472_);
lean_dec_ref(v_a_5471_);
lean_dec(v_a_5470_);
lean_dec_ref(v_a_5469_);
lean_dec(v_a_5468_);
lean_dec_ref(v_a_5467_);
lean_dec(v_a_5466_);
lean_dec(v_a_5465_);
lean_dec_ref(v_a_5464_);
return v_res_5476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; 
v___x_5478_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_5479_ = l_Lean_stringToMessageData(v___x_5478_);
return v___x_5479_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2));
v___x_5482_ = l_Lean_stringToMessageData(v___x_5481_);
return v___x_5482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5484_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_5485_ = l_Lean_stringToMessageData(v___x_5484_);
return v___x_5485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5487_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6));
v___x_5488_ = l_Lean_stringToMessageData(v___x_5487_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_5491_, lean_object* v_scope_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_){
_start:
{
lean_object* v_scope_5506_; lean_object* v_gs_5507_; lean_object* v_g_5511_; lean_object* v_gs_5517_; lean_object* v___y_5521_; lean_object* v___y_5522_; lean_object* v___y_5527_; lean_object* v_gs_5528_; lean_object* v___y_5532_; lean_object* v_g_5533_; lean_object* v___y_5534_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; lean_object* v___y_5600_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v___y_5604_; lean_object* v___y_5605_; lean_object* v___y_5606_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___x_5710_; 
v___x_5710_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_5494_);
if (lean_obj_tag(v___x_5710_) == 0)
{
lean_object* v_a_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5958_; 
v_a_5711_ = lean_ctor_get(v___x_5710_, 0);
v_isSharedCheck_5958_ = !lean_is_exclusive(v___x_5710_);
if (v_isSharedCheck_5958_ == 0)
{
v___x_5713_ = v___x_5710_;
v_isShared_5714_ = v_isSharedCheck_5958_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_a_5711_);
lean_dec(v___x_5710_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5958_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
uint8_t v___x_5715_; 
v___x_5715_ = lean_unbox(v_a_5711_);
lean_dec(v_a_5711_);
if (v___x_5715_ == 0)
{
lean_object* v___x_5716_; 
lean_del_object(v___x_5713_);
lean_inc(v_goal_5491_);
v___x_5716_ = l_Lean_MVarId_getType(v_goal_5491_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
if (lean_obj_tag(v___x_5716_) == 0)
{
lean_object* v_a_5717_; lean_object* v___x_5719_; uint8_t v_isShared_5720_; uint8_t v_isSharedCheck_5945_; 
v_a_5717_ = lean_ctor_get(v___x_5716_, 0);
v_isSharedCheck_5945_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5945_ == 0)
{
v___x_5719_ = v___x_5716_;
v_isShared_5720_ = v_isSharedCheck_5945_;
goto v_resetjp_5718_;
}
else
{
lean_inc(v_a_5717_);
lean_dec(v___x_5716_);
v___x_5719_ = lean_box(0);
v_isShared_5720_ = v_isSharedCheck_5945_;
goto v_resetjp_5718_;
}
v_resetjp_5718_:
{
lean_object* v_options_5727_; lean_object* v_inheritedTraceOptions_5728_; uint8_t v_hasTrace_5729_; lean_object* v___x_5730_; lean_object* v___y_5732_; lean_object* v___y_5733_; lean_object* v___y_5734_; lean_object* v___y_5735_; lean_object* v___y_5736_; lean_object* v___y_5737_; lean_object* v___y_5738_; lean_object* v___y_5739_; lean_object* v___y_5740_; lean_object* v___y_5741_; lean_object* v___y_5742_; 
v_options_5727_ = lean_ctor_get(v___y_5502_, 2);
v_inheritedTraceOptions_5728_ = lean_ctor_get(v___y_5502_, 13);
v_hasTrace_5729_ = lean_ctor_get_uint8(v_options_5727_, sizeof(void*)*1);
v___x_5730_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_5729_ == 0)
{
v___y_5732_ = v___y_5493_;
v___y_5733_ = v___y_5494_;
v___y_5734_ = v___y_5495_;
v___y_5735_ = v___y_5496_;
v___y_5736_ = v___y_5497_;
v___y_5737_ = v___y_5498_;
v___y_5738_ = v___y_5499_;
v___y_5739_ = v___y_5500_;
v___y_5740_ = v___y_5501_;
v___y_5741_ = v___y_5502_;
v___y_5742_ = v___y_5503_;
goto v___jp_5731_;
}
else
{
lean_object* v___x_5931_; uint8_t v___x_5932_; 
v___x_5931_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5932_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5728_, v_options_5727_, v___x_5931_);
if (v___x_5932_ == 0)
{
v___y_5732_ = v___y_5493_;
v___y_5733_ = v___y_5494_;
v___y_5734_ = v___y_5495_;
v___y_5735_ = v___y_5496_;
v___y_5736_ = v___y_5497_;
v___y_5737_ = v___y_5498_;
v___y_5738_ = v___y_5499_;
v___y_5739_ = v___y_5500_;
v___y_5740_ = v___y_5501_;
v___y_5741_ = v___y_5502_;
v___y_5742_ = v___y_5503_;
goto v___jp_5731_;
}
else
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; 
v___x_5933_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_5717_);
v___x_5934_ = l_Lean_MessageData_ofExpr(v_a_5717_);
v___x_5935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set(v___x_5935_, 1, v___x_5934_);
v___x_5936_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5730_, v___x_5935_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
if (lean_obj_tag(v___x_5936_) == 0)
{
lean_dec_ref_known(v___x_5936_, 1);
v___y_5732_ = v___y_5493_;
v___y_5733_ = v___y_5494_;
v___y_5734_ = v___y_5495_;
v___y_5735_ = v___y_5496_;
v___y_5736_ = v___y_5497_;
v___y_5737_ = v___y_5498_;
v___y_5738_ = v___y_5499_;
v___y_5739_ = v___y_5500_;
v___y_5740_ = v___y_5501_;
v___y_5741_ = v___y_5502_;
v___y_5742_ = v___y_5503_;
goto v___jp_5731_;
}
else
{
lean_object* v_a_5937_; lean_object* v___x_5939_; uint8_t v_isShared_5940_; uint8_t v_isSharedCheck_5944_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5937_ = lean_ctor_get(v___x_5936_, 0);
v_isSharedCheck_5944_ = !lean_is_exclusive(v___x_5936_);
if (v_isSharedCheck_5944_ == 0)
{
v___x_5939_ = v___x_5936_;
v_isShared_5940_ = v_isSharedCheck_5944_;
goto v_resetjp_5938_;
}
else
{
lean_inc(v_a_5937_);
lean_dec(v___x_5936_);
v___x_5939_ = lean_box(0);
v_isShared_5940_ = v_isSharedCheck_5944_;
goto v_resetjp_5938_;
}
v_resetjp_5938_:
{
lean_object* v___x_5942_; 
if (v_isShared_5940_ == 0)
{
v___x_5942_ = v___x_5939_;
goto v_reusejp_5941_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v_a_5937_);
v___x_5942_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5941_;
}
v_reusejp_5941_:
{
return v___x_5942_;
}
}
}
}
}
v___jp_5721_:
{
lean_object* v___x_5722_; lean_object* v___x_5723_; lean_object* v___x_5725_; 
v___x_5722_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5722_, 0, v_a_5717_);
v___x_5723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
if (v_isShared_5720_ == 0)
{
lean_ctor_set(v___x_5719_, 0, v___x_5723_);
v___x_5725_ = v___x_5719_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v___x_5723_);
v___x_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
return v___x_5725_;
}
}
v___jp_5731_:
{
lean_object* v___x_5743_; 
lean_inc(v_goal_5491_);
v___x_5743_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_5491_, v_a_5717_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5743_) == 0)
{
lean_object* v_a_5744_; 
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
lean_inc(v_a_5744_);
lean_dec_ref_known(v___x_5743_, 1);
if (lean_obj_tag(v_a_5744_) == 1)
{
lean_object* v_val_5745_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_val_5745_ = lean_ctor_get(v_a_5744_, 0);
lean_inc(v_val_5745_);
lean_dec_ref_known(v_a_5744_, 1);
v_gs_5517_ = v_val_5745_;
goto v___jp_5516_;
}
else
{
lean_object* v___x_5746_; 
lean_dec(v_a_5744_);
lean_inc(v_a_5717_);
lean_inc(v_goal_5491_);
v___x_5746_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_5491_, v_a_5717_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5746_) == 0)
{
lean_object* v_a_5747_; 
v_a_5747_ = lean_ctor_get(v___x_5746_, 0);
lean_inc(v_a_5747_);
lean_dec_ref_known(v___x_5746_, 1);
if (lean_obj_tag(v_a_5747_) == 1)
{
lean_object* v_val_5748_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_val_5748_ = lean_ctor_get(v_a_5747_, 0);
lean_inc(v_val_5748_);
lean_dec_ref_known(v_a_5747_, 1);
v_g_5511_ = v_val_5748_;
goto v___jp_5510_;
}
else
{
lean_object* v___x_5749_; 
lean_dec(v_a_5747_);
lean_inc(v_goal_5491_);
v___x_5749_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_5491_, v_a_5717_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5749_) == 0)
{
lean_object* v_a_5750_; 
v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
lean_inc(v_a_5750_);
lean_dec_ref_known(v___x_5749_, 1);
if (lean_obj_tag(v_a_5750_) == 1)
{
lean_object* v_val_5751_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_val_5751_ = lean_ctor_get(v_a_5750_, 0);
lean_inc(v_val_5751_);
lean_dec_ref_known(v_a_5750_, 1);
v_g_5511_ = v_val_5751_;
goto v___jp_5510_;
}
else
{
lean_object* v___x_5752_; 
lean_dec(v_a_5750_);
lean_inc(v_a_5717_);
lean_inc(v_goal_5491_);
v___x_5752_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_5491_, v_a_5717_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5752_) == 0)
{
lean_object* v_a_5753_; 
v_a_5753_ = lean_ctor_get(v___x_5752_, 0);
lean_inc(v_a_5753_);
lean_dec_ref_known(v___x_5752_, 1);
if (lean_obj_tag(v_a_5753_) == 1)
{
lean_object* v_val_5754_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_val_5754_ = lean_ctor_get(v_a_5753_, 0);
lean_inc(v_val_5754_);
lean_dec_ref_known(v_a_5753_, 1);
v_g_5511_ = v_val_5754_;
goto v___jp_5510_;
}
else
{
lean_object* v___x_5755_; 
lean_dec(v_a_5753_);
lean_inc(v_a_5717_);
lean_inc(v_goal_5491_);
lean_inc_ref(v_scope_5492_);
v___x_5755_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_5492_, v_goal_5491_, v_a_5717_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5755_) == 0)
{
lean_object* v_a_5756_; 
v_a_5756_ = lean_ctor_get(v___x_5755_, 0);
lean_inc(v_a_5756_);
lean_dec_ref_known(v___x_5755_, 1);
if (lean_obj_tag(v_a_5756_) == 1)
{
lean_object* v_val_5757_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_val_5757_ = lean_ctor_get(v_a_5756_, 0);
lean_inc(v_val_5757_);
lean_dec_ref_known(v_a_5756_, 1);
v_gs_5517_ = v_val_5757_;
goto v___jp_5516_;
}
else
{
lean_object* v___x_5758_; uint8_t v___x_5759_; 
lean_dec(v_a_5756_);
lean_inc(v_a_5717_);
v___x_5758_ = l_Lean_Expr_cleanupAnnotations(v_a_5717_);
v___x_5759_ = l_Lean_Expr_isApp(v___x_5758_);
if (v___x_5759_ == 0)
{
lean_dec_ref(v___x_5758_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
goto v___jp_5721_;
}
else
{
lean_object* v_arg_5760_; lean_object* v___x_5761_; uint8_t v___x_5762_; 
v_arg_5760_ = lean_ctor_get(v___x_5758_, 1);
lean_inc_ref(v_arg_5760_);
v___x_5761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5758_);
v___x_5762_ = l_Lean_Expr_isApp(v___x_5761_);
if (v___x_5762_ == 0)
{
lean_dec_ref(v___x_5761_);
lean_dec_ref(v_arg_5760_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
goto v___jp_5721_;
}
else
{
lean_object* v_arg_5763_; lean_object* v___x_5764_; uint8_t v___x_5765_; 
v_arg_5763_ = lean_ctor_get(v___x_5761_, 1);
lean_inc_ref(v_arg_5763_);
v___x_5764_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5761_);
v___x_5765_ = l_Lean_Expr_isApp(v___x_5764_);
if (v___x_5765_ == 0)
{
lean_dec_ref(v___x_5764_);
lean_dec_ref(v_arg_5763_);
lean_dec_ref(v_arg_5760_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
goto v___jp_5721_;
}
else
{
lean_object* v_arg_5766_; lean_object* v___x_5767_; uint8_t v___x_5768_; 
v_arg_5766_ = lean_ctor_get(v___x_5764_, 1);
lean_inc_ref(v_arg_5766_);
v___x_5767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5764_);
v___x_5768_ = l_Lean_Expr_isApp(v___x_5767_);
if (v___x_5768_ == 0)
{
lean_dec_ref(v___x_5767_);
lean_dec_ref(v_arg_5766_);
lean_dec_ref(v_arg_5763_);
lean_dec_ref(v_arg_5760_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
goto v___jp_5721_;
}
else
{
lean_object* v_arg_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; uint8_t v___x_5772_; 
v_arg_5769_ = lean_ctor_get(v___x_5767_, 1);
lean_inc_ref(v_arg_5769_);
v___x_5770_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5767_);
v___x_5771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5772_ = l_Lean_Expr_isConstOf(v___x_5770_, v___x_5771_);
lean_dec_ref(v___x_5770_);
if (v___x_5772_ == 0)
{
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec_ref(v_arg_5763_);
lean_dec_ref(v_arg_5760_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
goto v___jp_5721_;
}
else
{
lean_object* v___x_5773_; 
lean_del_object(v___x_5719_);
v___x_5773_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_5763_, v___y_5740_);
if (lean_obj_tag(v___x_5773_) == 0)
{
lean_object* v_a_5774_; lean_object* v___x_5775_; 
v_a_5774_ = lean_ctor_get(v___x_5773_, 0);
lean_inc(v_a_5774_);
lean_dec_ref_known(v___x_5773_, 1);
v___x_5775_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_5760_, v___y_5740_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; lean_object* v___x_5777_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
lean_inc(v_a_5776_);
lean_dec_ref_known(v___x_5775_, 1);
lean_inc(v_goal_5491_);
v___x_5777_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_5491_, v___y_5732_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5777_) == 0)
{
lean_object* v_a_5778_; 
v_a_5778_ = lean_ctor_get(v___x_5777_, 0);
lean_inc(v_a_5778_);
lean_dec_ref_known(v___x_5777_, 1);
if (lean_obj_tag(v_a_5778_) == 1)
{
lean_object* v_val_5779_; 
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_val_5779_ = lean_ctor_get(v_a_5778_, 0);
lean_inc(v_val_5779_);
lean_dec_ref_known(v_a_5778_, 1);
v_gs_5517_ = v_val_5779_;
goto v___jp_5516_;
}
else
{
lean_object* v___x_5780_; 
lean_dec(v_a_5778_);
lean_inc(v_a_5717_);
lean_inc(v_a_5774_);
lean_inc(v_goal_5491_);
lean_inc_ref(v_scope_5492_);
v___x_5780_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_5492_, v_goal_5491_, v_arg_5769_, v_a_5774_, v_a_5717_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5780_) == 0)
{
lean_object* v_a_5781_; 
v_a_5781_ = lean_ctor_get(v___x_5780_, 0);
lean_inc(v_a_5781_);
lean_dec_ref_known(v___x_5780_, 1);
if (lean_obj_tag(v_a_5781_) == 1)
{
lean_object* v_val_5782_; lean_object* v_fst_5783_; lean_object* v_snd_5784_; 
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_val_5782_ = lean_ctor_get(v_a_5781_, 0);
lean_inc(v_val_5782_);
lean_dec_ref_known(v_a_5781_, 1);
v_fst_5783_ = lean_ctor_get(v_val_5782_, 0);
lean_inc(v_fst_5783_);
v_snd_5784_ = lean_ctor_get(v_val_5782_, 1);
lean_inc(v_snd_5784_);
lean_dec(v_val_5782_);
v_scope_5506_ = v_fst_5783_;
v_gs_5507_ = v_snd_5784_;
goto v___jp_5505_;
}
else
{
lean_object* v___x_5785_; 
lean_dec(v_a_5781_);
lean_inc(v_goal_5491_);
v___x_5785_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_5492_, v_goal_5491_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5785_) == 0)
{
lean_object* v_a_5786_; lean_object* v___x_5787_; 
v_a_5786_ = lean_ctor_get(v___x_5785_, 0);
lean_inc(v_a_5786_);
lean_dec_ref_known(v___x_5785_, 1);
lean_inc(v_a_5776_);
lean_inc(v_a_5774_);
lean_inc_ref(v_arg_5769_);
lean_inc(v_goal_5491_);
v___x_5787_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_5491_, v_a_5717_, v_arg_5769_, v_arg_5766_, v_a_5774_, v_a_5776_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5787_) == 0)
{
lean_object* v_a_5788_; lean_object* v___x_5790_; uint8_t v_isShared_5791_; uint8_t v_isSharedCheck_5842_; 
v_a_5788_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5790_ = v___x_5787_;
v_isShared_5791_ = v_isSharedCheck_5842_;
goto v_resetjp_5789_;
}
else
{
lean_inc(v_a_5788_);
lean_dec(v___x_5787_);
v___x_5790_ = lean_box(0);
v_isShared_5791_ = v_isSharedCheck_5842_;
goto v_resetjp_5789_;
}
v_resetjp_5789_:
{
if (lean_obj_tag(v_a_5788_) == 1)
{
lean_object* v_val_5792_; lean_object* v___x_5793_; lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5797_; 
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec(v_goal_5491_);
v_val_5792_ = lean_ctor_get(v_a_5788_, 0);
lean_inc(v_val_5792_);
lean_dec_ref_known(v_a_5788_, 1);
v___x_5793_ = lean_box(0);
v___x_5794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5794_, 0, v_val_5792_);
lean_ctor_set(v___x_5794_, 1, v___x_5793_);
v___x_5795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5795_, 0, v_a_5786_);
lean_ctor_set(v___x_5795_, 1, v___x_5794_);
if (v_isShared_5791_ == 0)
{
lean_ctor_set(v___x_5790_, 0, v___x_5795_);
v___x_5797_ = v___x_5790_;
goto v_reusejp_5796_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v___x_5795_);
v___x_5797_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5796_;
}
v_reusejp_5796_:
{
return v___x_5797_;
}
}
else
{
lean_object* v___x_5799_; 
lean_del_object(v___x_5790_);
lean_dec(v_a_5788_);
lean_inc(v_a_5776_);
lean_inc(v_goal_5491_);
v___x_5799_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_5491_, v_a_5776_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5799_) == 0)
{
lean_object* v_a_5800_; 
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
lean_inc(v_a_5800_);
lean_dec_ref_known(v___x_5799_, 1);
if (lean_obj_tag(v_a_5800_) == 1)
{
lean_object* v_val_5801_; 
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec(v_goal_5491_);
v_val_5801_ = lean_ctor_get(v_a_5800_, 0);
lean_inc(v_val_5801_);
lean_dec_ref_known(v_a_5800_, 1);
v___y_5527_ = v_a_5786_;
v_gs_5528_ = v_val_5801_;
goto v___jp_5526_;
}
else
{
lean_object* v___x_5802_; 
lean_dec(v_a_5800_);
lean_inc(v_a_5776_);
lean_inc(v_a_5774_);
lean_inc(v_goal_5491_);
lean_inc(v_a_5786_);
v___x_5802_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_a_5786_, v_goal_5491_, v_arg_5769_, v_a_5774_, v_a_5776_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
lean_dec_ref(v_arg_5769_);
if (lean_obj_tag(v___x_5802_) == 0)
{
lean_object* v_a_5803_; 
v_a_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_a_5803_);
lean_dec_ref_known(v___x_5802_, 1);
if (lean_obj_tag(v_a_5803_) == 1)
{
lean_object* v_val_5804_; 
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec(v_goal_5491_);
v_val_5804_ = lean_ctor_get(v_a_5803_, 0);
lean_inc(v_val_5804_);
lean_dec_ref_known(v_a_5803_, 1);
v___y_5527_ = v_a_5786_;
v_gs_5528_ = v_val_5804_;
goto v___jp_5526_;
}
else
{
lean_object* v___x_5805_; 
lean_dec(v_a_5803_);
lean_inc(v_a_5776_);
v___x_5805_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(v_a_5776_);
if (lean_obj_tag(v___x_5805_) == 1)
{
lean_object* v_options_5806_; uint8_t v_hasTrace_5807_; 
v_options_5806_ = lean_ctor_get(v___y_5741_, 2);
v_hasTrace_5807_ = lean_ctor_get_uint8(v_options_5806_, sizeof(void*)*1);
if (v_hasTrace_5807_ == 0)
{
lean_object* v_val_5808_; 
v_val_5808_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_val_5808_);
lean_dec_ref_known(v___x_5805_, 1);
v___y_5594_ = v_a_5786_;
v___y_5595_ = v_a_5774_;
v___y_5596_ = v_val_5808_;
v___y_5597_ = v_a_5776_;
v___y_5598_ = v___y_5732_;
v___y_5599_ = v___y_5733_;
v___y_5600_ = v___y_5734_;
v___y_5601_ = v___y_5735_;
v___y_5602_ = v___y_5736_;
v___y_5603_ = v___y_5737_;
v___y_5604_ = v___y_5738_;
v___y_5605_ = v___y_5739_;
v___y_5606_ = v___y_5740_;
v___y_5607_ = v___y_5741_;
v___y_5608_ = v___y_5742_;
goto v___jp_5593_;
}
else
{
lean_object* v_val_5809_; lean_object* v_inheritedTraceOptions_5810_; lean_object* v___x_5811_; uint8_t v___x_5812_; 
v_val_5809_ = lean_ctor_get(v___x_5805_, 0);
lean_inc(v_val_5809_);
lean_dec_ref_known(v___x_5805_, 1);
v_inheritedTraceOptions_5810_ = lean_ctor_get(v___y_5741_, 13);
v___x_5811_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5810_, v_options_5806_, v___x_5811_);
if (v___x_5812_ == 0)
{
v___y_5594_ = v_a_5786_;
v___y_5595_ = v_a_5774_;
v___y_5596_ = v_val_5809_;
v___y_5597_ = v_a_5776_;
v___y_5598_ = v___y_5732_;
v___y_5599_ = v___y_5733_;
v___y_5600_ = v___y_5734_;
v___y_5601_ = v___y_5735_;
v___y_5602_ = v___y_5736_;
v___y_5603_ = v___y_5737_;
v___y_5604_ = v___y_5738_;
v___y_5605_ = v___y_5739_;
v___y_5606_ = v___y_5740_;
v___y_5607_ = v___y_5741_;
v___y_5608_ = v___y_5742_;
goto v___jp_5593_;
}
else
{
lean_object* v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5813_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5);
v___x_5814_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_val_5809_);
v___x_5815_ = l_Lean_MessageData_ofExpr(v___x_5814_);
v___x_5816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5816_, 0, v___x_5813_);
lean_ctor_set(v___x_5816_, 1, v___x_5815_);
v___x_5817_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5730_, v___x_5816_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_);
if (lean_obj_tag(v___x_5817_) == 0)
{
lean_dec_ref_known(v___x_5817_, 1);
v___y_5594_ = v_a_5786_;
v___y_5595_ = v_a_5774_;
v___y_5596_ = v_val_5809_;
v___y_5597_ = v_a_5776_;
v___y_5598_ = v___y_5732_;
v___y_5599_ = v___y_5733_;
v___y_5600_ = v___y_5734_;
v___y_5601_ = v___y_5735_;
v___y_5602_ = v___y_5736_;
v___y_5603_ = v___y_5737_;
v___y_5604_ = v___y_5738_;
v___y_5605_ = v___y_5739_;
v___y_5606_ = v___y_5740_;
v___y_5607_ = v___y_5741_;
v___y_5608_ = v___y_5742_;
goto v___jp_5593_;
}
else
{
lean_object* v_a_5818_; lean_object* v___x_5820_; uint8_t v_isShared_5821_; uint8_t v_isSharedCheck_5825_; 
lean_dec(v_val_5809_);
lean_dec(v_a_5786_);
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec(v_goal_5491_);
v_a_5818_ = lean_ctor_get(v___x_5817_, 0);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5817_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5820_ = v___x_5817_;
v_isShared_5821_ = v_isSharedCheck_5825_;
goto v_resetjp_5819_;
}
else
{
lean_inc(v_a_5818_);
lean_dec(v___x_5817_);
v___x_5820_ = lean_box(0);
v_isShared_5821_ = v_isSharedCheck_5825_;
goto v_resetjp_5819_;
}
v_resetjp_5819_:
{
lean_object* v___x_5823_; 
if (v_isShared_5821_ == 0)
{
v___x_5823_ = v___x_5820_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_a_5818_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
}
}
}
}
else
{
lean_dec(v___x_5805_);
lean_dec(v_a_5786_);
lean_dec(v_goal_5491_);
v___y_5521_ = v_a_5774_;
v___y_5522_ = v_a_5776_;
goto v___jp_5520_;
}
}
}
else
{
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5833_; 
lean_dec(v_a_5786_);
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec(v_goal_5491_);
v_a_5826_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5833_ == 0)
{
v___x_5828_ = v___x_5802_;
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5802_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5831_; 
if (v_isShared_5829_ == 0)
{
v___x_5831_ = v___x_5828_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
}
}
}
else
{
lean_object* v_a_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5841_; 
lean_dec(v_a_5786_);
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec(v_goal_5491_);
v_a_5834_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5841_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5841_ == 0)
{
v___x_5836_ = v___x_5799_;
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_a_5834_);
lean_dec(v___x_5799_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5841_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5839_; 
if (v_isShared_5837_ == 0)
{
v___x_5839_ = v___x_5836_;
goto v_reusejp_5838_;
}
else
{
lean_object* v_reuseFailAlloc_5840_; 
v_reuseFailAlloc_5840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5840_, 0, v_a_5834_);
v___x_5839_ = v_reuseFailAlloc_5840_;
goto v_reusejp_5838_;
}
v_reusejp_5838_:
{
return v___x_5839_;
}
}
}
}
}
}
else
{
lean_object* v_a_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5850_; 
lean_dec(v_a_5786_);
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec(v_goal_5491_);
v_a_5843_ = lean_ctor_get(v___x_5787_, 0);
v_isSharedCheck_5850_ = !lean_is_exclusive(v___x_5787_);
if (v_isSharedCheck_5850_ == 0)
{
v___x_5845_ = v___x_5787_;
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_a_5843_);
lean_dec(v___x_5787_);
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
}
else
{
lean_object* v_a_5851_; lean_object* v___x_5853_; uint8_t v_isShared_5854_; uint8_t v_isSharedCheck_5858_; 
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec(v_a_5717_);
lean_dec(v_goal_5491_);
v_a_5851_ = lean_ctor_get(v___x_5785_, 0);
v_isSharedCheck_5858_ = !lean_is_exclusive(v___x_5785_);
if (v_isSharedCheck_5858_ == 0)
{
v___x_5853_ = v___x_5785_;
v_isShared_5854_ = v_isSharedCheck_5858_;
goto v_resetjp_5852_;
}
else
{
lean_inc(v_a_5851_);
lean_dec(v___x_5785_);
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
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5859_ = lean_ctor_get(v___x_5780_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5780_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5861_ = v___x_5780_;
v_isShared_5862_ = v_isSharedCheck_5866_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_a_5859_);
lean_dec(v___x_5780_);
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
lean_dec(v_a_5776_);
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5867_ = lean_ctor_get(v___x_5777_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v___x_5777_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5869_ = v___x_5777_;
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5777_);
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
else
{
lean_object* v_a_5875_; lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5882_; 
lean_dec(v_a_5774_);
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5875_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5877_ = v___x_5775_;
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
else
{
lean_inc(v_a_5875_);
lean_dec(v___x_5775_);
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
else
{
lean_object* v_a_5883_; lean_object* v___x_5885_; uint8_t v_isShared_5886_; uint8_t v_isSharedCheck_5890_; 
lean_dec_ref(v_arg_5769_);
lean_dec_ref(v_arg_5766_);
lean_dec_ref(v_arg_5760_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5883_ = lean_ctor_get(v___x_5773_, 0);
v_isSharedCheck_5890_ = !lean_is_exclusive(v___x_5773_);
if (v_isSharedCheck_5890_ == 0)
{
v___x_5885_ = v___x_5773_;
v_isShared_5886_ = v_isSharedCheck_5890_;
goto v_resetjp_5884_;
}
else
{
lean_inc(v_a_5883_);
lean_dec(v___x_5773_);
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
}
}
}
}
}
}
else
{
lean_object* v_a_5891_; lean_object* v___x_5893_; uint8_t v_isShared_5894_; uint8_t v_isSharedCheck_5898_; 
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5891_ = lean_ctor_get(v___x_5755_, 0);
v_isSharedCheck_5898_ = !lean_is_exclusive(v___x_5755_);
if (v_isSharedCheck_5898_ == 0)
{
v___x_5893_ = v___x_5755_;
v_isShared_5894_ = v_isSharedCheck_5898_;
goto v_resetjp_5892_;
}
else
{
lean_inc(v_a_5891_);
lean_dec(v___x_5755_);
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
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5899_ = lean_ctor_get(v___x_5752_, 0);
v_isSharedCheck_5906_ = !lean_is_exclusive(v___x_5752_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5901_ = v___x_5752_;
v_isShared_5902_ = v_isSharedCheck_5906_;
goto v_resetjp_5900_;
}
else
{
lean_inc(v_a_5899_);
lean_dec(v___x_5752_);
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
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5907_ = lean_ctor_get(v___x_5749_, 0);
v_isSharedCheck_5914_ = !lean_is_exclusive(v___x_5749_);
if (v_isSharedCheck_5914_ == 0)
{
v___x_5909_ = v___x_5749_;
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_a_5907_);
lean_dec(v___x_5749_);
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
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5915_ = lean_ctor_get(v___x_5746_, 0);
v_isSharedCheck_5922_ = !lean_is_exclusive(v___x_5746_);
if (v_isSharedCheck_5922_ == 0)
{
v___x_5917_ = v___x_5746_;
v_isShared_5918_ = v_isSharedCheck_5922_;
goto v_resetjp_5916_;
}
else
{
lean_inc(v_a_5915_);
lean_dec(v___x_5746_);
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
lean_del_object(v___x_5719_);
lean_dec(v_a_5717_);
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5923_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5930_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5930_ == 0)
{
v___x_5925_ = v___x_5743_;
v_isShared_5926_ = v_isSharedCheck_5930_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_a_5923_);
lean_dec(v___x_5743_);
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
}
}
else
{
lean_object* v_a_5946_; lean_object* v___x_5948_; uint8_t v_isShared_5949_; uint8_t v_isSharedCheck_5953_; 
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5946_ = lean_ctor_get(v___x_5716_, 0);
v_isSharedCheck_5953_ = !lean_is_exclusive(v___x_5716_);
if (v_isSharedCheck_5953_ == 0)
{
v___x_5948_ = v___x_5716_;
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
else
{
lean_inc(v_a_5946_);
lean_dec(v___x_5716_);
v___x_5948_ = lean_box(0);
v_isShared_5949_ = v_isSharedCheck_5953_;
goto v_resetjp_5947_;
}
v_resetjp_5947_:
{
lean_object* v___x_5951_; 
if (v_isShared_5949_ == 0)
{
v___x_5951_ = v___x_5948_;
goto v_reusejp_5950_;
}
else
{
lean_object* v_reuseFailAlloc_5952_; 
v_reuseFailAlloc_5952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5952_, 0, v_a_5946_);
v___x_5951_ = v_reuseFailAlloc_5952_;
goto v_reusejp_5950_;
}
v_reusejp_5950_:
{
return v___x_5951_;
}
}
}
}
else
{
lean_object* v___x_5954_; lean_object* v___x_5956_; 
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v___x_5954_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
if (v_isShared_5714_ == 0)
{
lean_ctor_set(v___x_5713_, 0, v___x_5954_);
v___x_5956_ = v___x_5713_;
goto v_reusejp_5955_;
}
else
{
lean_object* v_reuseFailAlloc_5957_; 
v_reuseFailAlloc_5957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5957_, 0, v___x_5954_);
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
lean_dec_ref(v_scope_5492_);
lean_dec(v_goal_5491_);
v_a_5959_ = lean_ctor_get(v___x_5710_, 0);
v_isSharedCheck_5966_ = !lean_is_exclusive(v___x_5710_);
if (v_isSharedCheck_5966_ == 0)
{
v___x_5961_ = v___x_5710_;
v_isShared_5962_ = v_isSharedCheck_5966_;
goto v_resetjp_5960_;
}
else
{
lean_inc(v_a_5959_);
lean_dec(v___x_5710_);
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
v___jp_5505_:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5508_, 0, v_scope_5506_);
lean_ctor_set(v___x_5508_, 1, v_gs_5507_);
v___x_5509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5508_);
return v___x_5509_;
}
v___jp_5510_:
{
lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5512_ = lean_box(0);
v___x_5513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5513_, 0, v_g_5511_);
lean_ctor_set(v___x_5513_, 1, v___x_5512_);
v___x_5514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5514_, 0, v_scope_5492_);
lean_ctor_set(v___x_5514_, 1, v___x_5513_);
v___x_5515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5515_, 0, v___x_5514_);
return v___x_5515_;
}
v___jp_5516_:
{
lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5518_, 0, v_scope_5492_);
lean_ctor_set(v___x_5518_, 1, v_gs_5517_);
v___x_5519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5518_);
return v___x_5519_;
}
v___jp_5520_:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; 
v___x_5523_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5523_, 0, v___y_5521_);
lean_ctor_set(v___x_5523_, 1, v___y_5522_);
v___x_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5524_, 0, v___x_5523_);
v___x_5525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5525_, 0, v___x_5524_);
return v___x_5525_;
}
v___jp_5526_:
{
lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5529_, 0, v___y_5527_);
lean_ctor_set(v___x_5529_, 1, v_gs_5528_);
v___x_5530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5530_, 0, v___x_5529_);
return v___x_5530_;
}
v___jp_5531_:
{
lean_object* v___x_5535_; 
v___x_5535_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5534_);
if (lean_obj_tag(v___x_5535_) == 0)
{
lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5545_; 
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5535_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; 
v_unused_5546_ = lean_ctor_get(v___x_5535_, 0);
lean_dec(v_unused_5546_);
v___x_5537_ = v___x_5535_;
v_isShared_5538_ = v_isSharedCheck_5545_;
goto v_resetjp_5536_;
}
else
{
lean_dec(v___x_5535_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5545_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5543_; 
v___x_5539_ = lean_box(0);
v___x_5540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5540_, 0, v_g_5533_);
lean_ctor_set(v___x_5540_, 1, v___x_5539_);
v___x_5541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5541_, 0, v___y_5532_);
lean_ctor_set(v___x_5541_, 1, v___x_5540_);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 0, v___x_5541_);
v___x_5543_ = v___x_5537_;
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
else
{
lean_object* v_a_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5554_; 
lean_dec(v_g_5533_);
lean_dec_ref(v___y_5532_);
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
v___jp_5555_:
{
lean_object* v___x_5569_; 
v___x_5569_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5567_);
if (lean_obj_tag(v___x_5569_) == 0)
{
lean_object* v___x_5570_; 
lean_dec_ref_known(v___x_5569_, 1);
lean_inc_ref(v___y_5556_);
v___x_5570_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(v___y_5556_, v_goal_5491_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5559_, v___y_5557_, v___y_5558_, v___y_5561_, v___y_5560_, v___y_5568_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_a_5571_);
lean_dec_ref_known(v___x_5570_, 1);
if (lean_obj_tag(v_a_5571_) == 0)
{
lean_object* v_scope_5572_; lean_object* v_subgoals_5573_; 
lean_dec_ref(v___y_5556_);
v_scope_5572_ = lean_ctor_get(v_a_5571_, 0);
lean_inc_ref(v_scope_5572_);
v_subgoals_5573_ = lean_ctor_get(v_a_5571_, 1);
lean_inc(v_subgoals_5573_);
lean_dec_ref_known(v_a_5571_, 2);
v_scope_5506_ = v_scope_5572_;
v_gs_5507_ = v_subgoals_5573_;
goto v___jp_5505_;
}
else
{
lean_object* v_goal_5574_; lean_object* v_info_5575_; lean_object* v___x_5576_; 
v_goal_5574_ = lean_ctor_get(v_a_5571_, 0);
lean_inc(v_goal_5574_);
v_info_5575_ = lean_ctor_get(v_a_5571_, 1);
lean_inc_ref(v_info_5575_);
lean_dec_ref_known(v_a_5571_, 2);
v___x_5576_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v___y_5556_, v_goal_5574_, v_info_5575_, v___y_5566_, v___y_5567_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5559_, v___y_5557_, v___y_5558_, v___y_5561_, v___y_5560_, v___y_5568_);
return v___x_5576_;
}
}
else
{
lean_object* v_a_5577_; lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5584_; 
lean_dec_ref(v___y_5556_);
v_a_5577_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5584_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5579_ = v___x_5570_;
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
else
{
lean_inc(v_a_5577_);
lean_dec(v___x_5570_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5584_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5582_; 
if (v_isShared_5580_ == 0)
{
v___x_5582_ = v___x_5579_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v_a_5577_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
else
{
lean_object* v_a_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5592_; 
lean_dec_ref(v___y_5565_);
lean_dec_ref(v___y_5556_);
lean_dec(v_goal_5491_);
v_a_5585_ = lean_ctor_get(v___x_5569_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5587_ = v___x_5569_;
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_a_5585_);
lean_dec(v___x_5569_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5592_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5590_; 
if (v_isShared_5588_ == 0)
{
v___x_5590_ = v___x_5587_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5585_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
}
}
v___jp_5593_:
{
lean_object* v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; 
lean_dec_ref(v___y_5597_);
lean_dec_ref(v___y_5595_);
v___x_5609_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v___y_5596_);
v___x_5610_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v___y_5596_);
lean_inc_ref(v___x_5610_);
lean_inc_ref(v___x_5609_);
v___x_5611_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v___x_5609_, v___x_5610_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
if (lean_obj_tag(v___x_5611_) == 0)
{
lean_object* v_a_5612_; lean_object* v___x_5614_; uint8_t v_isShared_5615_; uint8_t v_isSharedCheck_5701_; 
v_a_5612_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5701_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5701_ == 0)
{
v___x_5614_ = v___x_5611_;
v_isShared_5615_ = v_isSharedCheck_5701_;
goto v_resetjp_5613_;
}
else
{
lean_inc(v_a_5612_);
lean_dec(v___x_5611_);
v___x_5614_ = lean_box(0);
v_isShared_5615_ = v_isSharedCheck_5701_;
goto v_resetjp_5613_;
}
v_resetjp_5613_:
{
uint8_t v___x_5616_; 
v___x_5616_ = lean_unbox(v_a_5612_);
lean_dec(v_a_5612_);
if (v___x_5616_ == 0)
{
lean_object* v___x_5617_; 
lean_del_object(v___x_5614_);
lean_dec_ref(v___x_5609_);
lean_inc_ref(v___y_5596_);
lean_inc(v_goal_5491_);
v___x_5617_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_5491_, v___y_5596_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
lean_inc(v_a_5618_);
lean_dec_ref_known(v___x_5617_, 1);
if (lean_obj_tag(v_a_5618_) == 1)
{
lean_object* v_val_5619_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec(v_goal_5491_);
v_val_5619_ = lean_ctor_get(v_a_5618_, 0);
lean_inc(v_val_5619_);
lean_dec_ref_known(v_a_5618_, 1);
v___y_5532_ = v___y_5594_;
v_g_5533_ = v_val_5619_;
v___y_5534_ = v___y_5599_;
goto v___jp_5531_;
}
else
{
lean_object* v___x_5620_; 
lean_dec(v_a_5618_);
lean_inc_ref(v___y_5596_);
lean_inc(v_goal_5491_);
v___x_5620_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_5491_, v___y_5596_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v_a_5621_; 
v_a_5621_ = lean_ctor_get(v___x_5620_, 0);
lean_inc(v_a_5621_);
lean_dec_ref_known(v___x_5620_, 1);
if (lean_obj_tag(v_a_5621_) == 1)
{
lean_object* v_val_5622_; lean_object* v___x_5623_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec(v_goal_5491_);
v_val_5622_ = lean_ctor_get(v_a_5621_, 0);
lean_inc(v_val_5622_);
lean_dec_ref_known(v_a_5621_, 1);
v___x_5623_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5599_);
if (lean_obj_tag(v___x_5623_) == 0)
{
lean_object* v___x_5625_; uint8_t v_isShared_5626_; uint8_t v_isSharedCheck_5631_; 
v_isSharedCheck_5631_ = !lean_is_exclusive(v___x_5623_);
if (v_isSharedCheck_5631_ == 0)
{
lean_object* v_unused_5632_; 
v_unused_5632_ = lean_ctor_get(v___x_5623_, 0);
lean_dec(v_unused_5632_);
v___x_5625_ = v___x_5623_;
v_isShared_5626_ = v_isSharedCheck_5631_;
goto v_resetjp_5624_;
}
else
{
lean_dec(v___x_5623_);
v___x_5625_ = lean_box(0);
v_isShared_5626_ = v_isSharedCheck_5631_;
goto v_resetjp_5624_;
}
v_resetjp_5624_:
{
lean_object* v___x_5627_; lean_object* v___x_5629_; 
v___x_5627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5627_, 0, v___y_5594_);
lean_ctor_set(v___x_5627_, 1, v_val_5622_);
if (v_isShared_5626_ == 0)
{
lean_ctor_set(v___x_5625_, 0, v___x_5627_);
v___x_5629_ = v___x_5625_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
else
{
lean_object* v_a_5633_; lean_object* v___x_5635_; uint8_t v_isShared_5636_; uint8_t v_isSharedCheck_5640_; 
lean_dec(v_val_5622_);
lean_dec_ref(v___y_5594_);
v_a_5633_ = lean_ctor_get(v___x_5623_, 0);
v_isSharedCheck_5640_ = !lean_is_exclusive(v___x_5623_);
if (v_isSharedCheck_5640_ == 0)
{
v___x_5635_ = v___x_5623_;
v_isShared_5636_ = v_isSharedCheck_5640_;
goto v_resetjp_5634_;
}
else
{
lean_inc(v_a_5633_);
lean_dec(v___x_5623_);
v___x_5635_ = lean_box(0);
v_isShared_5636_ = v_isSharedCheck_5640_;
goto v_resetjp_5634_;
}
v_resetjp_5634_:
{
lean_object* v___x_5638_; 
if (v_isShared_5636_ == 0)
{
v___x_5638_ = v___x_5635_;
goto v_reusejp_5637_;
}
else
{
lean_object* v_reuseFailAlloc_5639_; 
v_reuseFailAlloc_5639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_a_5633_);
v___x_5638_ = v_reuseFailAlloc_5639_;
goto v_reusejp_5637_;
}
v_reusejp_5637_:
{
return v___x_5638_;
}
}
}
}
else
{
lean_object* v___x_5641_; 
lean_dec(v_a_5621_);
lean_inc_ref(v___y_5596_);
lean_inc(v_goal_5491_);
v___x_5641_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_5491_, v___y_5596_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
if (lean_obj_tag(v___x_5641_) == 0)
{
lean_object* v_a_5642_; 
v_a_5642_ = lean_ctor_get(v___x_5641_, 0);
lean_inc(v_a_5642_);
lean_dec_ref_known(v___x_5641_, 1);
if (lean_obj_tag(v_a_5642_) == 1)
{
lean_object* v_val_5643_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec(v_goal_5491_);
v_val_5643_ = lean_ctor_get(v_a_5642_, 0);
lean_inc(v_val_5643_);
lean_dec_ref_known(v_a_5642_, 1);
v___y_5532_ = v___y_5594_;
v_g_5533_ = v_val_5643_;
v___y_5534_ = v___y_5599_;
goto v___jp_5531_;
}
else
{
lean_object* v___x_5644_; 
lean_dec(v_a_5642_);
lean_inc_ref(v___y_5596_);
lean_inc(v_goal_5491_);
v___x_5644_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_5491_, v___y_5596_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
if (lean_obj_tag(v___x_5644_) == 0)
{
lean_object* v_a_5645_; 
v_a_5645_ = lean_ctor_get(v___x_5644_, 0);
lean_inc(v_a_5645_);
lean_dec_ref_known(v___x_5644_, 1);
if (lean_obj_tag(v_a_5645_) == 1)
{
lean_object* v_val_5646_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec(v_goal_5491_);
v_val_5646_ = lean_ctor_get(v_a_5645_, 0);
lean_inc(v_val_5646_);
lean_dec_ref_known(v_a_5645_, 1);
v___y_5532_ = v___y_5594_;
v_g_5533_ = v_val_5646_;
v___y_5534_ = v___y_5599_;
goto v___jp_5531_;
}
else
{
lean_object* v___x_5647_; uint8_t v___x_5648_; 
lean_dec(v_a_5645_);
v___x_5647_ = l_Lean_Expr_getAppFn(v___x_5610_);
v___x_5648_ = l_Lean_Expr_isConst(v___x_5647_);
if (v___x_5648_ == 0)
{
uint8_t v___x_5649_; 
v___x_5649_ = l_Lean_Expr_isFVar(v___x_5647_);
lean_dec_ref(v___x_5647_);
if (v___x_5649_ == 0)
{
lean_object* v___x_5650_; lean_object* v___x_5651_; lean_object* v___x_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v_a_5656_; lean_object* v___x_5658_; uint8_t v_isShared_5659_; uint8_t v_isSharedCheck_5663_; 
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v___x_5650_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v___x_5651_ = l_Lean_MessageData_ofExpr(v___x_5610_);
v___x_5652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5652_, 0, v___x_5650_);
lean_ctor_set(v___x_5652_, 1, v___x_5651_);
v___x_5653_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3);
v___x_5654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5652_);
lean_ctor_set(v___x_5654_, 1, v___x_5653_);
v___x_5655_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5654_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
v_isSharedCheck_5663_ = !lean_is_exclusive(v___x_5655_);
if (v_isSharedCheck_5663_ == 0)
{
v___x_5658_ = v___x_5655_;
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
else
{
lean_inc(v_a_5656_);
lean_dec(v___x_5655_);
v___x_5658_ = lean_box(0);
v_isShared_5659_ = v_isSharedCheck_5663_;
goto v_resetjp_5657_;
}
v_resetjp_5657_:
{
lean_object* v___x_5661_; 
if (v_isShared_5659_ == 0)
{
v___x_5661_ = v___x_5658_;
goto v_reusejp_5660_;
}
else
{
lean_object* v_reuseFailAlloc_5662_; 
v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
v___x_5661_ = v_reuseFailAlloc_5662_;
goto v_reusejp_5660_;
}
v_reusejp_5660_:
{
return v___x_5661_;
}
}
}
else
{
lean_dec_ref(v___x_5610_);
v___y_5556_ = v___y_5594_;
v___y_5557_ = v___y_5604_;
v___y_5558_ = v___y_5605_;
v___y_5559_ = v___y_5603_;
v___y_5560_ = v___y_5607_;
v___y_5561_ = v___y_5606_;
v___y_5562_ = v___y_5600_;
v___y_5563_ = v___y_5601_;
v___y_5564_ = v___y_5602_;
v___y_5565_ = v___y_5596_;
v___y_5566_ = v___y_5598_;
v___y_5567_ = v___y_5599_;
v___y_5568_ = v___y_5608_;
goto v___jp_5555_;
}
}
else
{
lean_dec_ref(v___x_5647_);
lean_dec_ref(v___x_5610_);
v___y_5556_ = v___y_5594_;
v___y_5557_ = v___y_5604_;
v___y_5558_ = v___y_5605_;
v___y_5559_ = v___y_5603_;
v___y_5560_ = v___y_5607_;
v___y_5561_ = v___y_5606_;
v___y_5562_ = v___y_5600_;
v___y_5563_ = v___y_5601_;
v___y_5564_ = v___y_5602_;
v___y_5565_ = v___y_5596_;
v___y_5566_ = v___y_5598_;
v___y_5567_ = v___y_5599_;
v___y_5568_ = v___y_5608_;
goto v___jp_5555_;
}
}
}
else
{
lean_object* v_a_5664_; lean_object* v___x_5666_; uint8_t v_isShared_5667_; uint8_t v_isSharedCheck_5671_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v_a_5664_ = lean_ctor_get(v___x_5644_, 0);
v_isSharedCheck_5671_ = !lean_is_exclusive(v___x_5644_);
if (v_isSharedCheck_5671_ == 0)
{
v___x_5666_ = v___x_5644_;
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
else
{
lean_inc(v_a_5664_);
lean_dec(v___x_5644_);
v___x_5666_ = lean_box(0);
v_isShared_5667_ = v_isSharedCheck_5671_;
goto v_resetjp_5665_;
}
v_resetjp_5665_:
{
lean_object* v___x_5669_; 
if (v_isShared_5667_ == 0)
{
v___x_5669_ = v___x_5666_;
goto v_reusejp_5668_;
}
else
{
lean_object* v_reuseFailAlloc_5670_; 
v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
v___x_5669_ = v_reuseFailAlloc_5670_;
goto v_reusejp_5668_;
}
v_reusejp_5668_:
{
return v___x_5669_;
}
}
}
}
}
else
{
lean_object* v_a_5672_; lean_object* v___x_5674_; uint8_t v_isShared_5675_; uint8_t v_isSharedCheck_5679_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v_a_5672_ = lean_ctor_get(v___x_5641_, 0);
v_isSharedCheck_5679_ = !lean_is_exclusive(v___x_5641_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5674_ = v___x_5641_;
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
else
{
lean_inc(v_a_5672_);
lean_dec(v___x_5641_);
v___x_5674_ = lean_box(0);
v_isShared_5675_ = v_isSharedCheck_5679_;
goto v_resetjp_5673_;
}
v_resetjp_5673_:
{
lean_object* v___x_5677_; 
if (v_isShared_5675_ == 0)
{
v___x_5677_ = v___x_5674_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5678_; 
v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
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
}
else
{
lean_object* v_a_5680_; lean_object* v___x_5682_; uint8_t v_isShared_5683_; uint8_t v_isSharedCheck_5687_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v_a_5680_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5687_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5687_ == 0)
{
v___x_5682_ = v___x_5620_;
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
else
{
lean_inc(v_a_5680_);
lean_dec(v___x_5620_);
v___x_5682_ = lean_box(0);
v_isShared_5683_ = v_isSharedCheck_5687_;
goto v_resetjp_5681_;
}
v_resetjp_5681_:
{
lean_object* v___x_5685_; 
if (v_isShared_5683_ == 0)
{
v___x_5685_ = v___x_5682_;
goto v_reusejp_5684_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v_a_5680_);
v___x_5685_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5684_;
}
v_reusejp_5684_:
{
return v___x_5685_;
}
}
}
}
}
else
{
lean_object* v_a_5688_; lean_object* v___x_5690_; uint8_t v_isShared_5691_; uint8_t v_isSharedCheck_5695_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v_a_5688_ = lean_ctor_get(v___x_5617_, 0);
v_isSharedCheck_5695_ = !lean_is_exclusive(v___x_5617_);
if (v_isSharedCheck_5695_ == 0)
{
v___x_5690_ = v___x_5617_;
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
else
{
lean_inc(v_a_5688_);
lean_dec(v___x_5617_);
v___x_5690_ = lean_box(0);
v_isShared_5691_ = v_isSharedCheck_5695_;
goto v_resetjp_5689_;
}
v_resetjp_5689_:
{
lean_object* v___x_5693_; 
if (v_isShared_5691_ == 0)
{
v___x_5693_ = v___x_5690_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5694_; 
v_reuseFailAlloc_5694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5694_, 0, v_a_5688_);
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
lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5699_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v___x_5696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5696_, 0, v___x_5609_);
v___x_5697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5697_, 0, v___x_5696_);
if (v_isShared_5615_ == 0)
{
lean_ctor_set(v___x_5614_, 0, v___x_5697_);
v___x_5699_ = v___x_5614_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5697_);
v___x_5699_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
return v___x_5699_;
}
}
}
}
else
{
lean_object* v_a_5702_; lean_object* v___x_5704_; uint8_t v_isShared_5705_; uint8_t v_isSharedCheck_5709_; 
lean_dec_ref(v___x_5610_);
lean_dec_ref(v___x_5609_);
lean_dec_ref(v___y_5596_);
lean_dec_ref(v___y_5594_);
lean_dec(v_goal_5491_);
v_a_5702_ = lean_ctor_get(v___x_5611_, 0);
v_isSharedCheck_5709_ = !lean_is_exclusive(v___x_5611_);
if (v_isSharedCheck_5709_ == 0)
{
v___x_5704_ = v___x_5611_;
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
else
{
lean_inc(v_a_5702_);
lean_dec(v___x_5611_);
v___x_5704_ = lean_box(0);
v_isShared_5705_ = v_isSharedCheck_5709_;
goto v_resetjp_5703_;
}
v_resetjp_5703_:
{
lean_object* v___x_5707_; 
if (v_isShared_5705_ == 0)
{
v___x_5707_ = v___x_5704_;
goto v_reusejp_5706_;
}
else
{
lean_object* v_reuseFailAlloc_5708_; 
v_reuseFailAlloc_5708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_a_5702_);
v___x_5707_ = v_reuseFailAlloc_5708_;
goto v_reusejp_5706_;
}
v_reusejp_5706_:
{
return v___x_5707_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_5967_, lean_object* v_scope_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_, lean_object* v___y_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_, lean_object* v___y_5977_, lean_object* v___y_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_){
_start:
{
lean_object* v_res_5981_; 
v_res_5981_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_5967_, v_scope_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_, v___y_5974_, v___y_5975_, v___y_5976_, v___y_5977_, v___y_5978_, v___y_5979_);
lean_dec(v___y_5979_);
lean_dec_ref(v___y_5978_);
lean_dec(v___y_5977_);
lean_dec_ref(v___y_5976_);
lean_dec(v___y_5975_);
lean_dec_ref(v___y_5974_);
lean_dec(v___y_5973_);
lean_dec_ref(v___y_5972_);
lean_dec(v___y_5971_);
lean_dec(v___y_5970_);
lean_dec_ref(v___y_5969_);
return v_res_5981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_scope_5982_, lean_object* v_goal_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_, lean_object* v_a_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_){
_start:
{
lean_object* v___f_5996_; lean_object* v___x_5997_; 
lean_inc(v_goal_5983_);
v___f_5996_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_5996_, 0, v_goal_5983_);
lean_closure_set(v___f_5996_, 1, v_scope_5982_);
v___x_5997_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5983_, v___f_5996_, v_a_5984_, v_a_5985_, v_a_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_, v_a_5991_, v_a_5992_, v_a_5993_, v_a_5994_);
return v___x_5997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_scope_5998_, lean_object* v_goal_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_, lean_object* v_a_6003_, lean_object* v_a_6004_, lean_object* v_a_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_){
_start:
{
lean_object* v_res_6012_; 
v_res_6012_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_5998_, v_goal_5999_, v_a_6000_, v_a_6001_, v_a_6002_, v_a_6003_, v_a_6004_, v_a_6005_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_, v_a_6010_);
lean_dec(v_a_6010_);
lean_dec_ref(v_a_6009_);
lean_dec(v_a_6008_);
lean_dec_ref(v_a_6007_);
lean_dec(v_a_6006_);
lean_dec_ref(v_a_6005_);
lean_dec(v_a_6004_);
lean_dec_ref(v_a_6003_);
lean_dec(v_a_6002_);
lean_dec(v_a_6001_);
lean_dec_ref(v_a_6000_);
return v_res_6012_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_RuleCache(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Entails(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InstantiateS(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_InferType(uint8_t builtin);
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
