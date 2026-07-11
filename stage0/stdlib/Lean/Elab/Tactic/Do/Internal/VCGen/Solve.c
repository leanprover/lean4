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
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Expr_consumeMData(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Failed to intro forall target "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2_value;
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
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_179_ = l_Lean_stringToMessageData(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(lean_object* v_goal_184_, lean_object* v_target_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___y_199_; lean_object* v___y_205_; lean_object* v___y_206_; lean_object* v___y_207_; lean_object* v___y_208_; lean_object* v___y_209_; lean_object* v___y_210_; lean_object* v___y_211_; lean_object* v___y_212_; lean_object* v___y_213_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; uint8_t v___y_218_; uint8_t v___x_231_; 
v___x_231_ = l_Lean_Expr_isForall(v_target_185_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_goal_184_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; 
lean_inc(v_goal_184_);
v___x_234_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_goal_184_, v_a_186_, v_a_187_, v_a_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v_a_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_272_; 
v_a_235_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_272_ == 0)
{
v___x_237_ = v___x_234_;
v_isShared_238_ = v_isSharedCheck_272_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_a_235_);
lean_dec(v___x_234_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_272_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_fst_240_; uint8_t v_snd_241_; lean_object* v___y_242_; lean_object* v___y_243_; lean_object* v___y_244_; lean_object* v___y_245_; lean_object* v___y_246_; lean_object* v___y_247_; lean_object* v___y_248_; lean_object* v___y_249_; lean_object* v___y_250_; lean_object* v___y_251_; lean_object* v___y_252_; 
switch(lean_obj_tag(v_a_235_))
{
case 0:
{
uint8_t v___x_266_; 
lean_del_object(v___x_237_);
v___x_266_ = 0;
v_fst_240_ = v_goal_184_;
v_snd_241_ = v___x_266_;
v___y_242_ = v_a_186_;
v___y_243_ = v_a_187_;
v___y_244_ = v_a_188_;
v___y_245_ = v_a_189_;
v___y_246_ = v_a_190_;
v___y_247_ = v_a_191_;
v___y_248_ = v_a_192_;
v___y_249_ = v_a_193_;
v___y_250_ = v_a_194_;
v___y_251_ = v_a_195_;
v___y_252_ = v_a_196_;
goto v___jp_239_;
}
case 1:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_goal_184_);
v___x_267_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v___x_267_);
v___x_269_ = v___x_237_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
default: 
{
lean_object* v_mvarId_271_; 
lean_del_object(v___x_237_);
lean_dec(v_goal_184_);
v_mvarId_271_ = lean_ctor_get(v_a_235_, 0);
lean_inc(v_mvarId_271_);
lean_dec_ref_known(v_a_235_, 1);
v_fst_240_ = v_mvarId_271_;
v_snd_241_ = v___x_231_;
v___y_242_ = v_a_186_;
v___y_243_ = v_a_187_;
v___y_244_ = v_a_188_;
v___y_245_ = v_a_189_;
v___y_246_ = v_a_190_;
v___y_247_ = v_a_191_;
v___y_248_ = v_a_192_;
v___y_249_ = v_a_193_;
v___y_250_ = v_a_194_;
v___y_251_ = v_a_195_;
v___y_252_ = v_a_196_;
goto v___jp_239_;
}
}
v___jp_239_:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2));
lean_inc(v_fst_240_);
v___x_254_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_fst_240_, v___x_253_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; uint8_t v___x_256_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_255_);
lean_dec_ref_known(v___x_254_, 1);
v___x_256_ = lean_bool_not(v_snd_241_);
if (v___x_256_ == 0)
{
v___y_205_ = v___y_242_;
v___y_206_ = v___y_245_;
v___y_207_ = v___y_246_;
v___y_208_ = v_a_255_;
v___y_209_ = v___y_249_;
v___y_210_ = v___y_252_;
v___y_211_ = v___y_243_;
v___y_212_ = v_fst_240_;
v___y_213_ = v___y_250_;
v___y_214_ = v___y_248_;
v___y_215_ = v___y_247_;
v___y_216_ = v___y_244_;
v___y_217_ = v___y_251_;
v___y_218_ = v___x_256_;
goto v___jp_204_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_instBEqMVarId_beq(v_a_255_, v_fst_240_);
v___y_205_ = v___y_242_;
v___y_206_ = v___y_245_;
v___y_207_ = v___y_246_;
v___y_208_ = v_a_255_;
v___y_209_ = v___y_249_;
v___y_210_ = v___y_252_;
v___y_211_ = v___y_243_;
v___y_212_ = v_fst_240_;
v___y_213_ = v___y_250_;
v___y_214_ = v___y_248_;
v___y_215_ = v___y_247_;
v___y_216_ = v___y_244_;
v___y_217_ = v___y_251_;
v___y_218_ = v___x_257_;
goto v___jp_204_;
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec(v_fst_240_);
v_a_258_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_254_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_254_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
}
else
{
lean_object* v_a_273_; lean_object* v___x_275_; uint8_t v_isShared_276_; uint8_t v_isSharedCheck_280_; 
lean_dec(v_goal_184_);
v_a_273_ = lean_ctor_get(v___x_234_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v___x_234_);
if (v_isSharedCheck_280_ == 0)
{
v___x_275_ = v___x_234_;
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
else
{
lean_inc(v_a_273_);
lean_dec(v___x_234_);
v___x_275_ = lean_box(0);
v_isShared_276_ = v_isSharedCheck_280_;
goto v_resetjp_274_;
}
v_resetjp_274_:
{
lean_object* v___x_278_; 
if (v_isShared_276_ == 0)
{
v___x_278_ = v___x_275_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_a_273_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
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
v___jp_204_:
{
if (v___y_218_ == 0)
{
lean_dec(v___y_212_);
v___y_199_ = v___y_208_;
goto v___jp_198_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v_a_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_230_; 
lean_dec(v___y_208_);
v___x_219_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__1);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v___y_212_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_221_, v___y_209_, v___y_213_, v___y_217_, v___y_210_);
v_a_223_ = lean_ctor_get(v___x_222_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v___x_222_);
if (v_isSharedCheck_230_ == 0)
{
v___x_225_ = v___x_222_;
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_a_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_230_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_228_; 
if (v_isShared_226_ == 0)
{
v___x_228_ = v___x_225_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_a_223_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___boxed(lean_object* v_goal_281_, lean_object* v_target_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_281_, v_target_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_a_293_);
lean_dec_ref(v_a_292_);
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec(v_a_284_);
lean_dec_ref(v_a_283_);
lean_dec_ref(v_target_282_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(lean_object* v_00_u03b1_296_, lean_object* v_msg_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v_msg_297_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___boxed(lean_object* v_00_u03b1_311_, lean_object* v_msg_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0(v_00_u03b1_311_, v_msg_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_325_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0));
v___x_328_ = l_Lean_stringToMessageData(v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__2));
v___x_331_ = l_Lean_stringToMessageData(v___x_330_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(lean_object* v_name_332_, lean_object* v_val_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
uint8_t v_useJP_343_; 
v_useJP_343_ = lean_ctor_get_uint8(v_a_334_, sizeof(void*)*4 + 1);
if (v_useJP_343_ == 0)
{
lean_dec(v_name_332_);
goto v___jp_340_;
}
else
{
uint8_t v___x_344_; 
v___x_344_ = l_Lean_Elab_Tactic_Do_isJP(v_name_332_);
if (v___x_344_ == 0)
{
lean_dec(v_name_332_);
goto v___jp_340_;
}
else
{
uint8_t v___x_345_; 
v___x_345_ = l_Lean_Expr_isLambda(v_val_333_);
if (v___x_345_ == 0)
{
lean_dec(v_name_332_);
goto v___jp_340_;
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_346_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__1);
v___x_347_ = l_Lean_MessageData_ofName(v_name_332_);
v___x_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__3);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_350_, v_a_335_, v_a_336_, v_a_337_, v_a_338_);
return v___x_351_;
}
}
}
v___jp_340_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(0);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___boxed(lean_object* v_name_352_, lean_object* v_val_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_name_352_, v_val_353_, v_a_354_, v_a_355_, v_a_356_, v_a_357_, v_a_358_);
lean_dec(v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec(v_a_356_);
lean_dec_ref(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_val_353_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(lean_object* v_name_361_, lean_object* v_val_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_name_361_, v_val_362_, v_a_363_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___boxed(lean_object* v_name_376_, lean_object* v_val_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP(v_name_376_, v_val_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec_ref(v_val_377_);
return v_res_390_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_391_; double v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_float_of_nat(v___x_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(lean_object* v_cls_396_, lean_object* v_msg_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_ref_403_; lean_object* v___x_404_; lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_449_; 
v_ref_403_ = lean_ctor_get(v___y_400_, 5);
v___x_404_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0_spec__0(v_msg_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
v_a_405_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_449_ == 0)
{
v___x_407_ = v___x_404_;
v_isShared_408_ = v_isSharedCheck_449_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_449_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v_traceState_410_; lean_object* v_env_411_; lean_object* v_nextMacroScope_412_; lean_object* v_ngen_413_; lean_object* v_auxDeclNGen_414_; lean_object* v_cache_415_; lean_object* v_messages_416_; lean_object* v_infoState_417_; lean_object* v_snapshotTasks_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_448_; 
v___x_409_ = lean_st_ref_take(v___y_401_);
v_traceState_410_ = lean_ctor_get(v___x_409_, 4);
v_env_411_ = lean_ctor_get(v___x_409_, 0);
v_nextMacroScope_412_ = lean_ctor_get(v___x_409_, 1);
v_ngen_413_ = lean_ctor_get(v___x_409_, 2);
v_auxDeclNGen_414_ = lean_ctor_get(v___x_409_, 3);
v_cache_415_ = lean_ctor_get(v___x_409_, 5);
v_messages_416_ = lean_ctor_get(v___x_409_, 6);
v_infoState_417_ = lean_ctor_get(v___x_409_, 7);
v_snapshotTasks_418_ = lean_ctor_get(v___x_409_, 8);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_448_ == 0)
{
v___x_420_ = v___x_409_;
v_isShared_421_ = v_isSharedCheck_448_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_snapshotTasks_418_);
lean_inc(v_infoState_417_);
lean_inc(v_messages_416_);
lean_inc(v_cache_415_);
lean_inc(v_traceState_410_);
lean_inc(v_auxDeclNGen_414_);
lean_inc(v_ngen_413_);
lean_inc(v_nextMacroScope_412_);
lean_inc(v_env_411_);
lean_dec(v___x_409_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_448_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
uint64_t v_tid_422_; lean_object* v_traces_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_447_; 
v_tid_422_ = lean_ctor_get_uint64(v_traceState_410_, sizeof(void*)*1);
v_traces_423_ = lean_ctor_get(v_traceState_410_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_traceState_410_);
if (v_isSharedCheck_447_ == 0)
{
v___x_425_ = v_traceState_410_;
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_traces_423_);
lean_dec(v_traceState_410_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_447_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; double v___x_428_; uint8_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
v___x_427_ = lean_box(0);
v___x_428_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__0);
v___x_429_ = 0;
v___x_430_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__1));
v___x_431_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_431_, 0, v_cls_396_);
lean_ctor_set(v___x_431_, 1, v___x_427_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set_float(v___x_431_, sizeof(void*)*3, v___x_428_);
lean_ctor_set_float(v___x_431_, sizeof(void*)*3 + 8, v___x_428_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*3 + 16, v___x_429_);
v___x_432_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___closed__2));
v___x_433_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_433_, 0, v___x_431_);
lean_ctor_set(v___x_433_, 1, v_a_405_);
lean_ctor_set(v___x_433_, 2, v___x_432_);
lean_inc(v_ref_403_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v_ref_403_);
lean_ctor_set(v___x_434_, 1, v___x_433_);
v___x_435_ = l_Lean_PersistentArray_push___redArg(v_traces_423_, v___x_434_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 0, v___x_435_);
v___x_437_ = v___x_425_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_435_);
lean_ctor_set_uint64(v_reuseFailAlloc_446_, sizeof(void*)*1, v_tid_422_);
v___x_437_ = v_reuseFailAlloc_446_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_421_ == 0)
{
lean_ctor_set(v___x_420_, 4, v___x_437_);
v___x_439_ = v___x_420_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_env_411_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_nextMacroScope_412_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_ngen_413_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v_auxDeclNGen_414_);
lean_ctor_set(v_reuseFailAlloc_445_, 4, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_445_, 5, v_cache_415_);
lean_ctor_set(v_reuseFailAlloc_445_, 6, v_messages_416_);
lean_ctor_set(v_reuseFailAlloc_445_, 7, v_infoState_417_);
lean_ctor_set(v_reuseFailAlloc_445_, 8, v_snapshotTasks_418_);
v___x_439_ = v_reuseFailAlloc_445_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_st_ref_set(v___y_401_, v___x_439_);
v___x_441_ = lean_box(0);
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 0, v___x_441_);
v___x_443_ = v___x_407_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg___boxed(lean_object* v_cls_450_, lean_object* v_msg_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_450_, v_msg_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
return v_res_457_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_471_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__6));
v___x_472_ = l_Lean_Name_append(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__8));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__10));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(lean_object* v_goal_479_, lean_object* v_target_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; 
if (lean_obj_tag(v_target_480_) == 8)
{
lean_object* v_declName_524_; lean_object* v_value_525_; lean_object* v_body_526_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___x_565_; 
v_declName_524_ = lean_ctor_get(v_target_480_, 0);
lean_inc_n(v_declName_524_, 2);
v_value_525_ = lean_ctor_get(v_target_480_, 2);
lean_inc_ref(v_value_525_);
v_body_526_ = lean_ctor_get(v_target_480_, 3);
lean_inc_ref(v_body_526_);
lean_dec_ref_known(v_target_480_, 4);
v___x_565_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_524_, v_value_525_, v_a_481_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_565_) == 0)
{
uint8_t v___x_566_; 
lean_dec_ref_known(v___x_565_, 1);
v___x_566_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_525_);
if (v___x_566_ == 0)
{
lean_object* v_options_567_; uint8_t v_hasTrace_568_; 
lean_dec_ref(v_body_526_);
lean_dec_ref(v_value_525_);
v_options_567_ = lean_ctor_get(v_a_490_, 2);
v_hasTrace_568_ = lean_ctor_get_uint8(v_options_567_, sizeof(void*)*1);
if (v_hasTrace_568_ == 0)
{
lean_dec(v_declName_524_);
v___y_494_ = v_a_481_;
v___y_495_ = v_a_482_;
v___y_496_ = v_a_483_;
v___y_497_ = v_a_484_;
v___y_498_ = v_a_485_;
v___y_499_ = v_a_486_;
v___y_500_ = v_a_487_;
v___y_501_ = v_a_488_;
v___y_502_ = v_a_489_;
v___y_503_ = v_a_490_;
v___y_504_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v_inheritedTraceOptions_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_inheritedTraceOptions_569_ = lean_ctor_get(v_a_490_, 13);
v___x_570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_571_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_572_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_569_, v_options_567_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec(v_declName_524_);
v___y_494_ = v_a_481_;
v___y_495_ = v_a_482_;
v___y_496_ = v_a_483_;
v___y_497_ = v_a_484_;
v___y_498_ = v_a_485_;
v___y_499_ = v_a_486_;
v___y_500_ = v_a_487_;
v___y_501_ = v_a_488_;
v___y_502_ = v_a_489_;
v___y_503_ = v_a_490_;
v___y_504_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__9);
v___x_574_ = l_Lean_MessageData_ofName(v_declName_524_);
v___x_575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_575_, 0, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_574_);
v___x_576_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_570_, v___x_575_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_dec_ref_known(v___x_576_, 1);
v___y_494_ = v_a_481_;
v___y_495_ = v_a_482_;
v___y_496_ = v_a_483_;
v___y_497_ = v_a_484_;
v___y_498_ = v_a_485_;
v___y_499_ = v_a_486_;
v___y_500_ = v_a_487_;
v___y_501_ = v_a_488_;
v___y_502_ = v_a_489_;
v___y_503_ = v_a_490_;
v___y_504_ = v_a_491_;
goto v___jp_493_;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec(v_goal_479_);
v_a_577_ = lean_ctor_get(v___x_576_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_576_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_576_);
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
}
}
else
{
lean_object* v_options_585_; uint8_t v_hasTrace_586_; 
v_options_585_ = lean_ctor_get(v_a_490_, 2);
v_hasTrace_586_ = lean_ctor_get_uint8(v_options_585_, sizeof(void*)*1);
if (v_hasTrace_586_ == 0)
{
lean_dec(v_declName_524_);
v___y_528_ = v_a_486_;
v___y_529_ = v_a_487_;
v___y_530_ = v_a_488_;
v___y_531_ = v_a_489_;
v___y_532_ = v_a_490_;
v___y_533_ = v_a_491_;
goto v___jp_527_;
}
else
{
lean_object* v_inheritedTraceOptions_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v_inheritedTraceOptions_587_ = lean_ctor_get(v_a_490_, 13);
v___x_588_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_590_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_587_, v_options_585_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec(v_declName_524_);
v___y_528_ = v_a_486_;
v___y_529_ = v_a_487_;
v___y_530_ = v_a_488_;
v___y_531_ = v_a_489_;
v___y_532_ = v_a_490_;
v___y_533_ = v_a_491_;
goto v___jp_527_;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_592_ = l_Lean_MessageData_ofName(v_declName_524_);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_588_, v___x_593_, v_a_488_, v_a_489_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_dec_ref_known(v___x_594_, 1);
v___y_528_ = v_a_486_;
v___y_529_ = v_a_487_;
v___y_530_ = v_a_488_;
v___y_531_ = v_a_489_;
v___y_532_ = v_a_490_;
v___y_533_ = v_a_491_;
goto v___jp_527_;
}
else
{
lean_object* v_a_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_body_526_);
lean_dec_ref(v_value_525_);
lean_dec(v_goal_479_);
v_a_595_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_602_ == 0)
{
v___x_597_ = v___x_594_;
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_a_595_);
lean_dec(v___x_594_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_602_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
if (v_isShared_598_ == 0)
{
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_a_595_);
v___x_600_ = v_reuseFailAlloc_601_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
return v___x_600_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_body_526_);
lean_dec_ref(v_value_525_);
lean_dec(v_declName_524_);
lean_dec(v_goal_479_);
v_a_603_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_565_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_565_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
v___jp_527_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_mk_empty_array_with_capacity(v___x_534_);
v___x_536_ = lean_array_push(v___x_535_, v_value_525_);
v___x_537_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_526_, v___x_536_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_479_, v_a_538_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_548_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_548_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_548_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v___x_546_; 
v___x_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_544_, 0, v_a_540_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v___x_544_);
v___x_546_ = v___x_542_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v___x_544_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
v_a_549_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_539_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_539_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
else
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_564_; 
lean_dec(v_goal_479_);
v_a_557_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_564_ == 0)
{
v___x_559_ = v___x_537_;
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_537_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_564_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_562_; 
if (v_isShared_560_ == 0)
{
v___x_562_ = v___x_559_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_a_557_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref(v_target_480_);
lean_dec(v_goal_479_);
v___x_611_ = lean_box(0);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
v___jp_493_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2));
v___x_506_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(v_goal_479_, v___x_505_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_515_; 
v_a_507_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_515_ == 0)
{
v___x_509_ = v___x_506_;
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_506_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_515_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v_a_507_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_511_);
v___x_513_ = v___x_509_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
v_a_516_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_506_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_506_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___boxed(lean_object* v_goal_613_, lean_object* v_target_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_613_, v_target_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
lean_dec(v_a_625_);
lean_dec_ref(v_a_624_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec(v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec(v_a_616_);
lean_dec_ref(v_a_615_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(lean_object* v_cls_628_, lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_628_, v_msg_629_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___boxed(lean_object* v_cls_643_, lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0(v_cls_643_, v_msg_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(lean_object* v_goal_666_, lean_object* v_target_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_680_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__3));
v___x_681_ = l_Lean_Expr_isAppOf(v_target_667_, v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_goal_666_);
v___x_682_ = lean_box(0);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
else
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(v_goal_666_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_693_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_693_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_693_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_689_, 0, v_a_685_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_689_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
v_a_694_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_684_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_684_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___boxed(lean_object* v_goal_702_, lean_object* v_target_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_702_, v_target_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec(v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec_ref(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec_ref(v_target_703_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
uint8_t v___y_729_; 
if (lean_obj_tag(v_x_725_) == 5)
{
lean_object* v_fn_738_; lean_object* v_arg_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v_fn_738_ = lean_ctor_get(v_x_725_, 0);
lean_inc_ref(v_fn_738_);
v_arg_739_ = lean_ctor_get(v_x_725_, 1);
lean_inc_ref(v_arg_739_);
lean_dec_ref_known(v_x_725_, 2);
v___x_740_ = lean_array_set(v_x_726_, v_x_727_, v_arg_739_);
v___x_741_ = lean_unsigned_to_nat(1u);
v___x_742_ = lean_nat_sub(v_x_727_, v___x_741_);
lean_dec(v_x_727_);
v_x_725_ = v_fn_738_;
v_x_726_ = v___x_740_;
v_x_727_ = v___x_742_;
goto _start;
}
else
{
lean_object* v___x_744_; uint8_t v___x_745_; 
lean_dec(v_x_727_);
v___x_744_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__2));
v___x_745_ = l_Lean_Expr_isConstOf(v_x_725_, v___x_744_);
if (v___x_745_ == 0)
{
v___y_729_ = v___x_745_;
goto v___jp_728_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_746_ = lean_unsigned_to_nat(10u);
v___x_747_ = lean_array_get_size(v_x_726_);
v___x_748_ = lean_nat_dec_le(v___x_746_, v___x_747_);
v___y_729_ = v___x_748_;
goto v___jp_728_;
}
}
v___jp_728_:
{
if (v___y_729_ == 0)
{
lean_object* v___x_730_; 
lean_dec_ref(v_x_726_);
lean_dec_ref(v_x_725_);
v___x_730_ = lean_box(0);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_731_ = lean_unsigned_to_nat(10u);
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = l_Array_extract___redArg(v_x_726_, v___x_732_, v___x_731_);
v___x_734_ = lean_array_get_size(v_x_726_);
v___x_735_ = l_Array_extract___redArg(v_x_726_, v___x_731_, v___x_734_);
lean_dec_ref(v_x_726_);
v___x_736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_736_, 0, v_x_725_);
lean_ctor_set(v___x_736_, 1, v___x_733_);
lean_ctor_set(v___x_736_, 2, v___x_735_);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0(void){
_start:
{
lean_object* v___x_749_; lean_object* v_dummy_750_; 
v___x_749_ = lean_box(0);
v_dummy_750_ = l_Lean_Expr_sort___override(v___x_749_);
return v_dummy_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(lean_object* v_rhs_751_){
_start:
{
lean_object* v_dummy_752_; lean_object* v_nargs_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v_dummy_752_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_753_ = l_Lean_Expr_getAppNumArgs(v_rhs_751_);
lean_inc(v_nargs_753_);
v___x_754_ = lean_mk_array(v_nargs_753_, v_dummy_752_);
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = lean_nat_sub(v_nargs_753_, v___x_755_);
lean_dec(v_nargs_753_);
v___x_757_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(v_rhs_751_, v___x_754_, v___x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
lean_object* v_ks_762_; lean_object* v_vs_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_787_; 
v_ks_762_ = lean_ctor_get(v_x_758_, 0);
v_vs_763_ = lean_ctor_get(v_x_758_, 1);
v_isSharedCheck_787_ = !lean_is_exclusive(v_x_758_);
if (v_isSharedCheck_787_ == 0)
{
v___x_765_ = v_x_758_;
v_isShared_766_ = v_isSharedCheck_787_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_vs_763_);
lean_inc(v_ks_762_);
lean_dec(v_x_758_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_787_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = lean_array_get_size(v_ks_762_);
v___x_768_ = lean_nat_dec_lt(v_x_759_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_dec(v_x_759_);
v___x_769_ = lean_array_push(v_ks_762_, v_x_760_);
v___x_770_ = lean_array_push(v_vs_763_, v_x_761_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_770_);
lean_ctor_set(v___x_765_, 0, v___x_769_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
else
{
lean_object* v_k_x27_774_; uint8_t v___x_775_; 
v_k_x27_774_ = lean_array_fget_borrowed(v_ks_762_, v_x_759_);
v___x_775_ = l_Lean_instBEqMVarId_beq(v_x_760_, v_k_x27_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_777_; 
if (v_isShared_766_ == 0)
{
v___x_777_ = v___x_765_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_ks_762_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_vs_763_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = lean_nat_add(v_x_759_, v___x_778_);
lean_dec(v_x_759_);
v_x_758_ = v___x_777_;
v_x_759_ = v___x_779_;
goto _start;
}
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_782_ = lean_array_fset(v_ks_762_, v_x_759_, v_x_760_);
v___x_783_ = lean_array_fset(v_vs_763_, v_x_759_, v_x_761_);
lean_dec(v_x_759_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v___x_783_);
lean_ctor_set(v___x_765_, 0, v___x_782_);
v___x_785_ = v___x_765_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_782_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_788_, lean_object* v_k_789_, lean_object* v_v_790_){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_788_, v___x_791_, v_k_789_, v_v_790_);
return v___x_792_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_794_, size_t v_x_795_, size_t v_x_796_, lean_object* v_x_797_, lean_object* v_x_798_){
_start:
{
if (lean_obj_tag(v_x_794_) == 0)
{
lean_object* v_es_799_; size_t v___x_800_; size_t v___x_801_; lean_object* v_j_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_es_799_ = lean_ctor_get(v_x_794_, 0);
v___x_800_ = ((size_t)31ULL);
v___x_801_ = lean_usize_land(v_x_795_, v___x_800_);
v_j_802_ = lean_usize_to_nat(v___x_801_);
v___x_803_ = lean_array_get_size(v_es_799_);
v___x_804_ = lean_nat_dec_lt(v_j_802_, v___x_803_);
if (v___x_804_ == 0)
{
lean_dec(v_j_802_);
lean_dec(v_x_798_);
lean_dec(v_x_797_);
return v_x_794_;
}
else
{
lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_843_; 
lean_inc_ref(v_es_799_);
v_isSharedCheck_843_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_843_ == 0)
{
lean_object* v_unused_844_; 
v_unused_844_ = lean_ctor_get(v_x_794_, 0);
lean_dec(v_unused_844_);
v___x_806_ = v_x_794_;
v_isShared_807_ = v_isSharedCheck_843_;
goto v_resetjp_805_;
}
else
{
lean_dec(v_x_794_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_843_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v_v_808_; lean_object* v___x_809_; lean_object* v_xs_x27_810_; lean_object* v___y_812_; 
v_v_808_ = lean_array_fget(v_es_799_, v_j_802_);
v___x_809_ = lean_box(0);
v_xs_x27_810_ = lean_array_fset(v_es_799_, v_j_802_, v___x_809_);
switch(lean_obj_tag(v_v_808_))
{
case 0:
{
lean_object* v_key_817_; lean_object* v_val_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_828_; 
v_key_817_ = lean_ctor_get(v_v_808_, 0);
v_val_818_ = lean_ctor_get(v_v_808_, 1);
v_isSharedCheck_828_ = !lean_is_exclusive(v_v_808_);
if (v_isSharedCheck_828_ == 0)
{
v___x_820_ = v_v_808_;
v_isShared_821_ = v_isSharedCheck_828_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_val_818_);
lean_inc(v_key_817_);
lean_dec(v_v_808_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_828_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_instBEqMVarId_beq(v_x_797_, v_key_817_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_del_object(v___x_820_);
v___x_823_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_817_, v_val_818_, v_x_797_, v_x_798_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___y_812_ = v___x_824_;
goto v___jp_811_;
}
else
{
lean_object* v___x_826_; 
lean_dec(v_val_818_);
lean_dec(v_key_817_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_x_798_);
lean_ctor_set(v___x_820_, 0, v_x_797_);
v___x_826_ = v___x_820_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_x_797_);
lean_ctor_set(v_reuseFailAlloc_827_, 1, v_x_798_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v___y_812_ = v___x_826_;
goto v___jp_811_;
}
}
}
}
case 1:
{
lean_object* v_node_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_841_; 
v_node_829_ = lean_ctor_get(v_v_808_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v_v_808_);
if (v_isSharedCheck_841_ == 0)
{
v___x_831_ = v_v_808_;
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_node_829_);
lean_dec(v_v_808_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_841_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
size_t v___x_833_; size_t v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_833_ = ((size_t)5ULL);
v___x_834_ = lean_usize_shift_right(v_x_795_, v___x_833_);
v___x_835_ = ((size_t)1ULL);
v___x_836_ = lean_usize_add(v_x_796_, v___x_835_);
v___x_837_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_829_, v___x_834_, v___x_836_, v_x_797_, v_x_798_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_837_);
v___x_839_ = v___x_831_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
v___y_812_ = v___x_839_;
goto v___jp_811_;
}
}
}
default: 
{
lean_object* v___x_842_; 
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v_x_797_);
lean_ctor_set(v___x_842_, 1, v_x_798_);
v___y_812_ = v___x_842_;
goto v___jp_811_;
}
}
v___jp_811_:
{
lean_object* v___x_813_; lean_object* v___x_815_; 
v___x_813_ = lean_array_fset(v_xs_x27_810_, v_j_802_, v___y_812_);
lean_dec(v_j_802_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 0, v___x_813_);
v___x_815_ = v___x_806_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
else
{
lean_object* v_ks_845_; lean_object* v_vs_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_866_; 
v_ks_845_ = lean_ctor_get(v_x_794_, 0);
v_vs_846_ = lean_ctor_get(v_x_794_, 1);
v_isSharedCheck_866_ = !lean_is_exclusive(v_x_794_);
if (v_isSharedCheck_866_ == 0)
{
v___x_848_ = v_x_794_;
v_isShared_849_ = v_isSharedCheck_866_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_vs_846_);
lean_inc(v_ks_845_);
lean_dec(v_x_794_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_866_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_ks_845_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_vs_846_);
v___x_851_ = v_reuseFailAlloc_865_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
lean_object* v_newNode_852_; uint8_t v___y_854_; size_t v___x_860_; uint8_t v___x_861_; 
v_newNode_852_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_851_, v_x_797_, v_x_798_);
v___x_860_ = ((size_t)7ULL);
v___x_861_ = lean_usize_dec_le(v___x_860_, v_x_796_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_852_);
v___x_863_ = lean_unsigned_to_nat(4u);
v___x_864_ = lean_nat_dec_lt(v___x_862_, v___x_863_);
lean_dec(v___x_862_);
v___y_854_ = v___x_864_;
goto v___jp_853_;
}
else
{
v___y_854_ = v___x_861_;
goto v___jp_853_;
}
v___jp_853_:
{
if (v___y_854_ == 0)
{
lean_object* v_ks_855_; lean_object* v_vs_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_ks_855_ = lean_ctor_get(v_newNode_852_, 0);
lean_inc_ref(v_ks_855_);
v_vs_856_ = lean_ctor_get(v_newNode_852_, 1);
lean_inc_ref(v_vs_856_);
lean_dec_ref(v_newNode_852_);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_859_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_796_, v_ks_855_, v_vs_856_, v___x_857_, v___x_858_);
lean_dec_ref(v_vs_856_);
lean_dec_ref(v_ks_855_);
return v___x_859_;
}
else
{
return v_newNode_852_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_867_, lean_object* v_keys_868_, lean_object* v_vals_869_, lean_object* v_i_870_, lean_object* v_entries_871_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_array_get_size(v_keys_868_);
v___x_873_ = lean_nat_dec_lt(v_i_870_, v___x_872_);
if (v___x_873_ == 0)
{
lean_dec(v_i_870_);
return v_entries_871_;
}
else
{
lean_object* v_k_874_; lean_object* v_v_875_; uint64_t v___x_876_; size_t v_h_877_; size_t v___x_878_; lean_object* v___x_879_; size_t v___x_880_; size_t v___x_881_; size_t v___x_882_; size_t v_h_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_k_874_ = lean_array_fget_borrowed(v_keys_868_, v_i_870_);
v_v_875_ = lean_array_fget_borrowed(v_vals_869_, v_i_870_);
v___x_876_ = l_Lean_instHashableMVarId_hash(v_k_874_);
v_h_877_ = lean_uint64_to_usize(v___x_876_);
v___x_878_ = ((size_t)5ULL);
v___x_879_ = lean_unsigned_to_nat(1u);
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_sub(v_depth_867_, v___x_880_);
v___x_882_ = lean_usize_mul(v___x_878_, v___x_881_);
v_h_883_ = lean_usize_shift_right(v_h_877_, v___x_882_);
v___x_884_ = lean_nat_add(v_i_870_, v___x_879_);
lean_dec(v_i_870_);
lean_inc(v_v_875_);
lean_inc(v_k_874_);
v___x_885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_871_, v_h_883_, v_depth_867_, v_k_874_, v_v_875_);
v_i_870_ = v___x_884_;
v_entries_871_ = v___x_885_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_887_, lean_object* v_keys_888_, lean_object* v_vals_889_, lean_object* v_i_890_, lean_object* v_entries_891_){
_start:
{
size_t v_depth_boxed_892_; lean_object* v_res_893_; 
v_depth_boxed_892_ = lean_unbox_usize(v_depth_887_);
lean_dec(v_depth_887_);
v_res_893_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_892_, v_keys_888_, v_vals_889_, v_i_890_, v_entries_891_);
lean_dec_ref(v_vals_889_);
lean_dec_ref(v_keys_888_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_x_896_, lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
size_t v_x_8514__boxed_899_; size_t v_x_8515__boxed_900_; lean_object* v_res_901_; 
v_x_8514__boxed_899_ = lean_unbox_usize(v_x_895_);
lean_dec(v_x_895_);
v_x_8515__boxed_900_ = lean_unbox_usize(v_x_896_);
lean_dec(v_x_896_);
v_res_901_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_894_, v_x_8514__boxed_899_, v_x_8515__boxed_900_, v_x_897_, v_x_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
uint64_t v___x_905_; size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_905_ = l_Lean_instHashableMVarId_hash(v_x_903_);
v___x_906_ = lean_uint64_to_usize(v___x_905_);
v___x_907_ = ((size_t)1ULL);
v___x_908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_902_, v___x_906_, v___x_907_, v_x_903_, v_x_904_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_909_, lean_object* v_val_910_, lean_object* v___y_911_){
_start:
{
lean_object* v___x_913_; lean_object* v_mctx_914_; lean_object* v_cache_915_; lean_object* v_zetaDeltaFVarIds_916_; lean_object* v_postponed_917_; lean_object* v_diag_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_946_; 
v___x_913_ = lean_st_ref_take(v___y_911_);
v_mctx_914_ = lean_ctor_get(v___x_913_, 0);
v_cache_915_ = lean_ctor_get(v___x_913_, 1);
v_zetaDeltaFVarIds_916_ = lean_ctor_get(v___x_913_, 2);
v_postponed_917_ = lean_ctor_get(v___x_913_, 3);
v_diag_918_ = lean_ctor_get(v___x_913_, 4);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_946_ == 0)
{
v___x_920_ = v___x_913_;
v_isShared_921_ = v_isSharedCheck_946_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_diag_918_);
lean_inc(v_postponed_917_);
lean_inc(v_zetaDeltaFVarIds_916_);
lean_inc(v_cache_915_);
lean_inc(v_mctx_914_);
lean_dec(v___x_913_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_946_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v_depth_922_; lean_object* v_levelAssignDepth_923_; lean_object* v_lmvarCounter_924_; lean_object* v_mvarCounter_925_; lean_object* v_lDecls_926_; lean_object* v_decls_927_; lean_object* v_userNames_928_; lean_object* v_lAssignment_929_; lean_object* v_eAssignment_930_; lean_object* v_dAssignment_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_945_; 
v_depth_922_ = lean_ctor_get(v_mctx_914_, 0);
v_levelAssignDepth_923_ = lean_ctor_get(v_mctx_914_, 1);
v_lmvarCounter_924_ = lean_ctor_get(v_mctx_914_, 2);
v_mvarCounter_925_ = lean_ctor_get(v_mctx_914_, 3);
v_lDecls_926_ = lean_ctor_get(v_mctx_914_, 4);
v_decls_927_ = lean_ctor_get(v_mctx_914_, 5);
v_userNames_928_ = lean_ctor_get(v_mctx_914_, 6);
v_lAssignment_929_ = lean_ctor_get(v_mctx_914_, 7);
v_eAssignment_930_ = lean_ctor_get(v_mctx_914_, 8);
v_dAssignment_931_ = lean_ctor_get(v_mctx_914_, 9);
v_isSharedCheck_945_ = !lean_is_exclusive(v_mctx_914_);
if (v_isSharedCheck_945_ == 0)
{
v___x_933_ = v_mctx_914_;
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_dAssignment_931_);
lean_inc(v_eAssignment_930_);
lean_inc(v_lAssignment_929_);
lean_inc(v_userNames_928_);
lean_inc(v_decls_927_);
lean_inc(v_lDecls_926_);
lean_inc(v_mvarCounter_925_);
lean_inc(v_lmvarCounter_924_);
lean_inc(v_levelAssignDepth_923_);
lean_inc(v_depth_922_);
lean_dec(v_mctx_914_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_945_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_930_, v_mvarId_909_, v_val_910_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 8, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_depth_922_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_levelAssignDepth_923_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_lmvarCounter_924_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_mvarCounter_925_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_lDecls_926_);
lean_ctor_set(v_reuseFailAlloc_944_, 5, v_decls_927_);
lean_ctor_set(v_reuseFailAlloc_944_, 6, v_userNames_928_);
lean_ctor_set(v_reuseFailAlloc_944_, 7, v_lAssignment_929_);
lean_ctor_set(v_reuseFailAlloc_944_, 8, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_944_, 9, v_dAssignment_931_);
v___x_937_ = v_reuseFailAlloc_944_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_937_);
v___x_939_ = v___x_920_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_cache_915_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_zetaDeltaFVarIds_916_);
lean_ctor_set(v_reuseFailAlloc_943_, 3, v_postponed_917_);
lean_ctor_set(v_reuseFailAlloc_943_, 4, v_diag_918_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_940_ = lean_st_ref_set(v___y_911_, v___x_939_);
v___x_941_ = lean_box(0);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
return v___x_942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_947_, lean_object* v_val_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_947_, v_val_948_, v___y_949_);
lean_dec(v___y_949_);
return v_res_951_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = l_Lean_Level_ofNat(v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; 
v___x_961_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4);
v___x_962_ = l_Lean_mkSort(v___x_961_);
return v___x_962_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = lean_box(0);
v___x_966_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6);
v___x_967_ = lean_unsigned_to_nat(2u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_array_push(v___x_968_, v___x_966_);
v___x_970_ = lean_array_push(v___x_969_, v___x_965_);
return v___x_970_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_box(0);
v___x_984_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12));
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(lean_object* v_goal_986_, lean_object* v_target_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc_ref(v_target_987_);
v___x_1000_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(v_target_987_);
if (lean_obj_tag(v___x_1000_) == 1)
{
lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1067_; 
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v___x_1000_, 0);
lean_dec(v_unused_1068_);
v___x_1002_ = v___x_1000_;
v_isShared_1003_ = v_isSharedCheck_1067_;
goto v_resetjp_1001_;
}
else
{
lean_dec(v___x_1000_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1067_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1005_ = lean_unsigned_to_nat(2u);
v___x_1006_ = lean_mk_empty_array_with_capacity(v___x_1005_);
v___x_1007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7);
v___x_1008_ = l_Lean_Meta_mkAppOptM(v___x_1004_, v___x_1007_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1008_) == 0)
{
lean_object* v_a_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec_ref_known(v___x_1008_, 1);
v___x_1010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_1011_ = lean_array_push(v___x_1006_, v_a_1009_);
lean_inc_ref(v_target_987_);
v___x_1012_ = lean_array_push(v___x_1011_, v_target_987_);
v___x_1013_ = l_Lean_Meta_mkAppM(v___x_1010_, v___x_1012_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = l_Lean_Meta_Sym_shareCommon(v_a_1014_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1016_, v___x_1017_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1033_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc_n(v_a_1019_, 2);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13);
v___x_1021_ = l_Lean_mkAppB(v___x_1020_, v_target_987_, v_a_1019_);
v___x_1022_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_986_, v___x_1021_, v_a_996_);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1033_ == 0)
{
lean_object* v_unused_1034_; 
v_unused_1034_ = lean_ctor_get(v___x_1022_, 0);
lean_dec(v_unused_1034_);
v___x_1024_ = v___x_1022_;
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
else
{
lean_dec(v___x_1022_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1033_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_Expr_mvarId_x21(v_a_1019_);
lean_dec(v_a_1019_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1026_);
v___x_1028_ = v___x_1002_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
lean_object* v___x_1030_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1028_);
v___x_1030_ = v___x_1024_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_del_object(v___x_1002_);
lean_dec_ref(v_target_987_);
lean_dec(v_goal_986_);
v_a_1035_ = lean_ctor_get(v___x_1018_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1018_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1018_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1018_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_del_object(v___x_1002_);
lean_dec_ref(v_target_987_);
lean_dec(v_goal_986_);
v_a_1043_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1015_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1015_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_del_object(v___x_1002_);
lean_dec_ref(v_target_987_);
lean_dec(v_goal_986_);
v_a_1051_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1013_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1013_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec_ref(v___x_1006_);
lean_del_object(v___x_1002_);
lean_dec_ref(v_target_987_);
lean_dec(v_goal_986_);
v_a_1059_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1008_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_1008_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
lean_dec(v___x_1000_);
lean_dec_ref(v_target_987_);
lean_dec(v_goal_986_);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
return v___x_1070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1071_, lean_object* v_target_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_1071_, v_target_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_);
lean_dec(v_a_1083_);
lean_dec_ref(v_a_1082_);
lean_dec(v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1086_, lean_object* v_val_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1086_, v_val_1087_, v___y_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1101_, lean_object* v_val_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1101_, v_val_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1116_, lean_object* v_x_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1117_, v_x_1118_, v_x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1121_, lean_object* v_x_1122_, size_t v_x_1123_, size_t v_x_1124_, lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1122_, v_x_1123_, v_x_1124_, v_x_1125_, v_x_1126_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1128_, lean_object* v_x_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
size_t v_x_9024__boxed_1134_; size_t v_x_9025__boxed_1135_; lean_object* v_res_1136_; 
v_x_9024__boxed_1134_ = lean_unbox_usize(v_x_1130_);
lean_dec(v_x_1130_);
v_x_9025__boxed_1135_ = lean_unbox_usize(v_x_1131_);
lean_dec(v_x_1131_);
v_res_1136_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1128_, v_x_1129_, v_x_9024__boxed_1134_, v_x_9025__boxed_1135_, v_x_1132_, v_x_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1137_, lean_object* v_n_1138_, lean_object* v_k_1139_, lean_object* v_v_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1138_, v_k_1139_, v_v_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1142_, size_t v_depth_1143_, lean_object* v_keys_1144_, lean_object* v_vals_1145_, lean_object* v_heq_1146_, lean_object* v_i_1147_, lean_object* v_entries_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1143_, v_keys_1144_, v_vals_1145_, v_i_1147_, v_entries_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1150_, lean_object* v_depth_1151_, lean_object* v_keys_1152_, lean_object* v_vals_1153_, lean_object* v_heq_1154_, lean_object* v_i_1155_, lean_object* v_entries_1156_){
_start:
{
size_t v_depth_boxed_1157_; lean_object* v_res_1158_; 
v_depth_boxed_1157_ = lean_unbox_usize(v_depth_1151_);
lean_dec(v_depth_1151_);
v_res_1158_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1150_, v_depth_boxed_1157_, v_keys_1152_, v_vals_1153_, v_heq_1154_, v_i_1155_, v_entries_1156_);
lean_dec_ref(v_vals_1153_);
lean_dec_ref(v_keys_1152_);
return v_res_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1160_, v_x_1161_, v_x_1162_, v_x_1163_);
return v___x_1164_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(lean_object* v_goal_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_backwardRules_1177_; lean_object* v_refl_1178_; lean_object* v___x_1179_; 
v_backwardRules_1177_ = lean_ctor_get(v_a_1169_, 0);
v_refl_1178_ = lean_ctor_get(v_backwardRules_1177_, 7);
lean_inc_ref(v_refl_1178_);
lean_inc(v_goal_1168_);
v___x_1179_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1168_, v_refl_1178_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1218_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1182_ = v___x_1179_;
v_isShared_1183_ = v_isSharedCheck_1218_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_a_1180_);
lean_dec(v___x_1179_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1218_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
if (lean_obj_tag(v_a_1180_) == 1)
{
lean_object* v_mvarIds_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1213_; 
v_mvarIds_1184_ = lean_ctor_get(v_a_1180_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v_a_1180_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1186_ = v_a_1180_;
v_isShared_1187_ = v_isSharedCheck_1213_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_mvarIds_1184_);
lean_dec(v_a_1180_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1213_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_options_1195_; uint8_t v_hasTrace_1196_; 
v_options_1195_ = lean_ctor_get(v_a_1174_, 2);
v_hasTrace_1196_ = lean_ctor_get_uint8(v_options_1195_, sizeof(void*)*1);
if (v_hasTrace_1196_ == 0)
{
lean_dec(v_goal_1168_);
goto v___jp_1188_;
}
else
{
lean_object* v_inheritedTraceOptions_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_inheritedTraceOptions_1197_ = lean_ctor_get(v_a_1174_, 13);
v___x_1198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1199_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1197_, v_options_1195_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_dec(v_goal_1168_);
goto v___jp_1188_;
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1201_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_goal_1168_);
v___x_1203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1202_);
v___x_1204_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1198_, v___x_1203_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_dec_ref_known(v___x_1204_, 1);
goto v___jp_1188_;
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_del_object(v___x_1186_);
lean_dec(v_mvarIds_1184_);
lean_del_object(v___x_1182_);
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
v___jp_1188_:
{
lean_object* v___x_1190_; 
if (v_isShared_1187_ == 0)
{
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_mvarIds_1184_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1190_);
v___x_1192_ = v___x_1182_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_dec(v_a_1180_);
lean_dec(v_goal_1168_);
v___x_1214_ = lean_box(0);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v___x_1214_);
v___x_1216_ = v___x_1182_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_goal_1168_);
v_a_1219_ = lean_ctor_get(v___x_1179_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1179_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1179_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1234_);
lean_dec_ref(v_a_1233_);
lean_dec(v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec_ref(v_a_1229_);
lean_dec_ref(v_a_1228_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(lean_object* v_goal_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1237_, v_a_1238_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___boxed(lean_object* v_goal_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(v_goal_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
lean_dec(v_a_1256_);
lean_dec_ref(v_a_1255_);
lean_dec(v_a_1254_);
lean_dec(v_a_1253_);
lean_dec_ref(v_a_1252_);
return v_res_1264_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1268_, lean_object* v_e_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1275_; 
v_lastLiftedPre_x3f_1275_ = lean_ctor_get(v_scope_1268_, 2);
lean_inc(v_lastLiftedPre_x3f_1275_);
lean_dec_ref(v_scope_1268_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1275_) == 1)
{
lean_object* v_val_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1331_; 
v_val_1276_ = lean_ctor_get(v_lastLiftedPre_x3f_1275_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1275_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1278_ = v_lastLiftedPre_x3f_1275_;
v_isShared_1279_ = v_isSharedCheck_1331_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_val_1276_);
lean_dec(v_lastLiftedPre_x3f_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1331_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_lctx_1280_; lean_object* v___x_1281_; 
v_lctx_1280_ = lean_ctor_get(v_a_1270_, 2);
lean_inc_ref(v_lctx_1280_);
v___x_1281_ = lean_local_ctx_find(v_lctx_1280_, v_val_1276_);
if (lean_obj_tag(v___x_1281_) == 1)
{
lean_object* v_val_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_val_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_val_1282_);
v___x_1283_ = l_Lean_LocalDecl_type(v_val_1282_);
v___x_1284_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_1269_, v___x_1283_);
lean_dec_ref(v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_val_1282_);
lean_del_object(v___x_1278_);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1281_, 0);
lean_dec(v_unused_1293_);
v___x_1286_ = v___x_1281_;
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
else
{
lean_dec(v___x_1281_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1292_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set_tag(v___x_1286_, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1288_);
v___x_1290_ = v___x_1286_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
lean_object* v_options_1294_; uint8_t v_hasTrace_1295_; 
v_options_1294_ = lean_ctor_get(v_a_1272_, 2);
v_hasTrace_1295_ = lean_ctor_get_uint8(v_options_1294_, sizeof(void*)*1);
if (v_hasTrace_1295_ == 0)
{
lean_object* v___x_1297_; 
lean_dec(v_val_1282_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1297_ = v___x_1278_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1281_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_inheritedTraceOptions_1299_ = lean_ctor_get(v_a_1272_, 13);
v___x_1300_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1301_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1302_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1299_, v_options_1294_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1304_; 
lean_dec(v_val_1282_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1281_);
v___x_1304_ = v___x_1278_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1281_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_del_object(v___x_1278_);
v___x_1306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1307_ = l_Lean_LocalDecl_userName(v_val_1282_);
lean_dec(v_val_1282_);
v___x_1308_ = l_Lean_MessageData_ofName(v___x_1307_);
v___x_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1306_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1300_, v___x_1309_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1310_, 0);
lean_dec(v_unused_1318_);
v___x_1312_ = v___x_1310_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_dec(v___x_1310_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 0, v___x_1281_);
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1281_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref_known(v___x_1281_, 1);
v_a_1319_ = lean_ctor_get(v___x_1310_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1310_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1310_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1310_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec(v___x_1281_);
v___x_1327_ = lean_box(0);
if (v_isShared_1279_ == 0)
{
lean_ctor_set_tag(v___x_1278_, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1327_);
v___x_1329_ = v___x_1278_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_lastLiftedPre_x3f_1275_);
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1334_, lean_object* v_e_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1334_, v_e_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
lean_dec(v_a_1339_);
lean_dec_ref(v_a_1338_);
lean_dec(v_a_1337_);
lean_dec_ref(v_a_1336_);
lean_dec_ref(v_e_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(lean_object* v_scope_1342_, lean_object* v_e_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
lean_object* v___x_1356_; 
v___x_1356_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1342_, v_e_1343_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
return v___x_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1357_, lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_){
_start:
{
lean_object* v_res_1371_; 
v_res_1371_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(v_scope_1357_, v_e_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
lean_dec(v_a_1367_);
lean_dec_ref(v_a_1366_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec_ref(v_e_1358_);
return v_res_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
lean_inc_ref(v___y_1376_);
lean_inc(v___y_1375_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
v___x_1385_ = lean_apply_12(v_x_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, lean_box(0));
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1400_, lean_object* v_x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___f_1414_; lean_object* v___x_1415_; 
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc_ref(v___y_1405_);
lean_inc(v___y_1404_);
lean_inc(v___y_1403_);
lean_inc_ref(v___y_1402_);
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1414_, 0, v_x_1401_);
lean_closure_set(v___f_1414_, 1, v___y_1402_);
lean_closure_set(v___f_1414_, 2, v___y_1403_);
lean_closure_set(v___f_1414_, 3, v___y_1404_);
lean_closure_set(v___f_1414_, 4, v___y_1405_);
lean_closure_set(v___f_1414_, 5, v___y_1406_);
lean_closure_set(v___f_1414_, 6, v___y_1407_);
lean_closure_set(v___f_1414_, 7, v___y_1408_);
v___x_1415_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1400_, v___f_1414_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1415_) == 0)
{
return v___x_1415_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1424_, v_x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1439_, lean_object* v_mvarId_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1440_, v_x_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1455_, lean_object* v_mvarId_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1455_, v_mvarId_1456_, v_x_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1476_, lean_object* v_scope_1477_, lean_object* v_rhs_1478_, lean_object* v_pre_1479_, lean_object* v_goal_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
if (v___x_1476_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
lean_dec(v_goal_1480_);
lean_dec_ref(v_pre_1479_);
lean_dec_ref(v_rhs_1478_);
lean_dec_ref(v_scope_1477_);
v___x_1493_ = lean_box(0);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
else
{
lean_object* v___x_1495_; 
v___x_1495_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1477_, v_rhs_1478_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1495_) == 0)
{
lean_object* v_a_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1532_; 
v_a_1496_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1498_ = v___x_1495_;
v_isShared_1499_ = v_isSharedCheck_1532_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_a_1496_);
lean_dec(v___x_1495_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1532_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
if (lean_obj_tag(v_a_1496_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1498_);
v_val_1500_ = lean_ctor_get(v_a_1496_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v_a_1496_, 1);
v___x_1501_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_1502_ = l_Lean_LocalDecl_toExpr(v_val_1500_);
v___x_1503_ = lean_unsigned_to_nat(3u);
v___x_1504_ = lean_mk_empty_array_with_capacity(v___x_1503_);
v___x_1505_ = lean_array_push(v___x_1504_, v_pre_1479_);
v___x_1506_ = lean_array_push(v___x_1505_, v_rhs_1478_);
v___x_1507_ = lean_array_push(v___x_1506_, v___x_1502_);
v___x_1508_ = l_Lean_Meta_mkAppM(v___x_1501_, v___x_1507_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1518_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc(v_a_1509_);
lean_dec_ref_known(v___x_1508_, 1);
v___x_1510_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1480_, v_a_1509_, v___y_1489_);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; 
v_unused_1519_ = lean_ctor_get(v___x_1510_, 0);
lean_dec(v_unused_1519_);
v___x_1512_ = v___x_1510_;
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
else
{
lean_dec(v___x_1510_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1518_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1514_; lean_object* v___x_1516_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v___x_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec(v_goal_1480_);
v_a_1520_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1508_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1508_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
}
else
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_dec(v_a_1496_);
lean_dec(v_goal_1480_);
lean_dec_ref(v_pre_1479_);
lean_dec_ref(v_rhs_1478_);
v___x_1528_ = lean_box(0);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v___x_1528_);
v___x_1530_ = v___x_1498_;
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
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
lean_dec(v_goal_1480_);
lean_dec_ref(v_pre_1479_);
lean_dec_ref(v_rhs_1478_);
v_a_1533_ = lean_ctor_get(v___x_1495_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1495_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v___x_1495_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v___x_1495_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_1541_ = _args[0];
lean_object* v_scope_1542_ = _args[1];
lean_object* v_rhs_1543_ = _args[2];
lean_object* v_pre_1544_ = _args[3];
lean_object* v_goal_1545_ = _args[4];
lean_object* v___y_1546_ = _args[5];
lean_object* v___y_1547_ = _args[6];
lean_object* v___y_1548_ = _args[7];
lean_object* v___y_1549_ = _args[8];
lean_object* v___y_1550_ = _args[9];
lean_object* v___y_1551_ = _args[10];
lean_object* v___y_1552_ = _args[11];
lean_object* v___y_1553_ = _args[12];
lean_object* v___y_1554_ = _args[13];
lean_object* v___y_1555_ = _args[14];
lean_object* v___y_1556_ = _args[15];
lean_object* v___y_1557_ = _args[16];
_start:
{
uint8_t v___x_7757__boxed_1558_; lean_object* v_res_1559_; 
v___x_7757__boxed_1558_ = lean_unbox(v___x_1541_);
v_res_1559_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1558_, v_scope_1542_, v_rhs_1543_, v_pre_1544_, v_goal_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(lean_object* v_scope_1560_, lean_object* v_goal_1561_, lean_object* v_00_u03b1_1562_, lean_object* v_pre_1563_, lean_object* v_rhs_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v_a_1569_, lean_object* v_a_1570_, lean_object* v_a_1571_, lean_object* v_a_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___y_1579_; lean_object* v___x_1580_; 
v___x_1577_ = l_Lean_Expr_isProp(v_00_u03b1_1562_);
v___x_1578_ = lean_box(v___x_1577_);
lean_inc(v_goal_1561_);
v___y_1579_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1579_, 0, v___x_1578_);
lean_closure_set(v___y_1579_, 1, v_scope_1560_);
lean_closure_set(v___y_1579_, 2, v_rhs_1564_);
lean_closure_set(v___y_1579_, 3, v_pre_1563_);
lean_closure_set(v___y_1579_, 4, v_goal_1561_);
v___x_1580_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1561_, v___y_1579_, v_a_1565_, v_a_1566_, v_a_1567_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_, v_a_1573_, v_a_1574_, v_a_1575_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_1581_ = _args[0];
lean_object* v_goal_1582_ = _args[1];
lean_object* v_00_u03b1_1583_ = _args[2];
lean_object* v_pre_1584_ = _args[3];
lean_object* v_rhs_1585_ = _args[4];
lean_object* v_a_1586_ = _args[5];
lean_object* v_a_1587_ = _args[6];
lean_object* v_a_1588_ = _args[7];
lean_object* v_a_1589_ = _args[8];
lean_object* v_a_1590_ = _args[9];
lean_object* v_a_1591_ = _args[10];
lean_object* v_a_1592_ = _args[11];
lean_object* v_a_1593_ = _args[12];
lean_object* v_a_1594_ = _args[13];
lean_object* v_a_1595_ = _args[14];
lean_object* v_a_1596_ = _args[15];
lean_object* v_a_1597_ = _args[16];
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_scope_1581_, v_goal_1582_, v_00_u03b1_1583_, v_pre_1584_, v_rhs_1585_, v_a_1586_, v_a_1587_, v_a_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec(v_a_1588_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec_ref(v_00_u03b1_1583_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1599_, lean_object* v_target_1600_, lean_object* v_goal_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1599_, v_target_1600_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1635_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1635_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1617_ = v___x_1614_;
v_isShared_1618_ = v_isSharedCheck_1635_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1614_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1635_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
if (lean_obj_tag(v_a_1615_) == 1)
{
lean_object* v_val_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1629_; 
lean_del_object(v___x_1617_);
v_val_1619_ = lean_ctor_get(v_a_1615_, 0);
lean_inc(v_val_1619_);
lean_dec_ref_known(v_a_1615_, 1);
v___x_1620_ = l_Lean_LocalDecl_toExpr(v_val_1619_);
v___x_1621_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1601_, v___x_1620_, v___y_1610_);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1629_ == 0)
{
lean_object* v_unused_1630_; 
v_unused_1630_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1630_);
v___x_1623_ = v___x_1621_;
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
else
{
lean_dec(v___x_1621_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1629_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1625_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1625_);
v___x_1627_ = v___x_1623_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
lean_dec(v_a_1615_);
lean_dec(v_goal_1601_);
v___x_1631_ = lean_box(0);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 0, v___x_1631_);
v___x_1633_ = v___x_1617_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1643_; 
lean_dec(v_goal_1601_);
v_a_1636_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1638_ = v___x_1614_;
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1614_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1643_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1636_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1644_, lean_object* v_target_1645_, lean_object* v_goal_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(v_scope_1644_, v_target_1645_, v_goal_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
lean_dec(v___y_1657_);
lean_dec_ref(v___y_1656_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec_ref(v_target_1645_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(lean_object* v_scope_1660_, lean_object* v_goal_1661_, lean_object* v_target_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___f_1675_; lean_object* v___x_1676_; 
lean_inc(v_goal_1661_);
v___f_1675_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1675_, 0, v_scope_1660_);
lean_closure_set(v___f_1675_, 1, v_target_1662_);
lean_closure_set(v___f_1675_, 2, v_goal_1661_);
v___x_1676_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1661_, v___f_1675_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1677_, lean_object* v_goal_1678_, lean_object* v_target_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_1677_, v_goal_1678_, v_target_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec(v_a_1690_);
lean_dec_ref(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec_ref(v_a_1687_);
lean_dec(v_a_1686_);
lean_dec_ref(v_a_1685_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
return v_res_1692_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_1701_, lean_object* v_pre_1702_, lean_object* v_a_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_, lean_object* v_a_1706_, lean_object* v_a_1707_, lean_object* v_a_1708_, lean_object* v_a_1709_, lean_object* v_a_1710_, lean_object* v_a_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1718_ = l_Lean_Expr_cleanupAnnotations(v_pre_1702_);
v___x_1719_ = l_Lean_Expr_isApp(v___x_1718_);
if (v___x_1719_ == 0)
{
lean_dec_ref(v___x_1718_);
lean_dec(v_goal_1701_);
goto v___jp_1715_;
}
else
{
lean_object* v_arg_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_arg_1720_ = lean_ctor_get(v___x_1718_, 1);
lean_inc_ref(v_arg_1720_);
v___x_1721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1718_);
v___x_1722_ = l_Lean_Expr_isApp(v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v___x_1721_);
lean_dec_ref(v_arg_1720_);
lean_dec(v_goal_1701_);
goto v___jp_1715_;
}
else
{
lean_object* v___x_1723_; uint8_t v___x_1724_; 
v___x_1723_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1721_);
v___x_1724_ = l_Lean_Expr_isApp(v___x_1723_);
if (v___x_1724_ == 0)
{
lean_dec_ref(v___x_1723_);
lean_dec_ref(v_arg_1720_);
lean_dec(v_goal_1701_);
goto v___jp_1715_;
}
else
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1723_);
v___x_1726_ = l_Lean_Expr_isApp(v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec_ref(v___x_1725_);
lean_dec_ref(v_arg_1720_);
lean_dec(v_goal_1701_);
goto v___jp_1715_;
}
else
{
lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1725_);
v___x_1728_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_1729_ = l_Lean_Expr_isConstOf(v___x_1727_, v___x_1728_);
lean_dec_ref(v___x_1727_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_arg_1720_);
lean_dec(v_goal_1701_);
goto v___jp_1715_;
}
else
{
lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1731_ = l_Lean_Expr_isAppOf(v_arg_1720_, v___x_1730_);
lean_dec_ref(v_arg_1720_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_goal_1701_);
v___x_1732_ = lean_box(0);
v___x_1733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
return v___x_1733_;
}
else
{
lean_object* v_backwardRules_1734_; lean_object* v_meetTop_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v_backwardRules_1734_ = lean_ctor_get(v_a_1703_, 0);
v_meetTop_1735_ = lean_ctor_get(v_backwardRules_1734_, 8);
v___x_1736_ = lean_box(0);
lean_inc(v_goal_1701_);
lean_inc_ref(v_meetTop_1735_);
v___x_1737_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_1735_, v_goal_1701_, v___x_1736_, v_a_1703_, v_a_1704_, v_a_1705_, v_a_1706_, v_a_1707_, v_a_1708_, v_a_1709_, v_a_1710_, v_a_1711_, v_a_1712_, v_a_1713_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1764_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1764_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1764_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; 
if (lean_obj_tag(v_a_1738_) == 1)
{
lean_object* v_mvarIds_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1763_; 
v_mvarIds_1751_ = lean_ctor_get(v_a_1738_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_a_1738_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1753_ = v_a_1738_;
v_isShared_1754_ = v_isSharedCheck_1763_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_mvarIds_1751_);
lean_dec(v_a_1738_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1763_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
if (lean_obj_tag(v_mvarIds_1751_) == 1)
{
lean_object* v_tail_1755_; 
v_tail_1755_ = lean_ctor_get(v_mvarIds_1751_, 1);
if (lean_obj_tag(v_tail_1755_) == 0)
{
lean_object* v_head_1756_; lean_object* v___x_1758_; 
lean_dec(v_goal_1701_);
v_head_1756_ = lean_ctor_get(v_mvarIds_1751_, 0);
lean_inc(v_head_1756_);
lean_dec_ref_known(v_mvarIds_1751_, 2);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v_head_1756_);
v___x_1758_ = v___x_1753_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_head_1756_);
v___x_1758_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
lean_object* v___x_1760_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1758_);
v___x_1760_ = v___x_1740_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1751_, 2);
lean_del_object(v___x_1753_);
lean_del_object(v___x_1740_);
v___y_1743_ = v_a_1710_;
v___y_1744_ = v_a_1711_;
v___y_1745_ = v_a_1712_;
v___y_1746_ = v_a_1713_;
goto v___jp_1742_;
}
}
else
{
lean_del_object(v___x_1753_);
lean_dec(v_mvarIds_1751_);
lean_del_object(v___x_1740_);
v___y_1743_ = v_a_1710_;
v___y_1744_ = v_a_1711_;
v___y_1745_ = v_a_1712_;
v___y_1746_ = v_a_1713_;
goto v___jp_1742_;
}
}
}
else
{
lean_del_object(v___x_1740_);
lean_dec(v_a_1738_);
v___y_1743_ = v_a_1710_;
v___y_1744_ = v_a_1711_;
v___y_1745_ = v_a_1712_;
v___y_1746_ = v_a_1713_;
goto v___jp_1742_;
}
v___jp_1742_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1748_, 0, v_goal_1701_);
v___x_1749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1747_);
lean_ctor_set(v___x_1749_, 1, v___x_1748_);
v___x_1750_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1749_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1750_;
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_goal_1701_);
v_a_1765_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1737_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1737_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
}
}
}
v___jp_1715_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_box(0);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v___x_1716_);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_1773_, lean_object* v_pre_1774_, lean_object* v_a_1775_, lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_1773_, v_pre_1774_, v_a_1775_, v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
lean_dec(v_a_1781_);
lean_dec_ref(v_a_1780_);
lean_dec(v_a_1779_);
lean_dec_ref(v_a_1778_);
lean_dec(v_a_1777_);
lean_dec(v_a_1776_);
lean_dec_ref(v_a_1775_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_1795_, lean_object* v_pre_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = l_Lean_Expr_cleanupAnnotations(v_pre_1796_);
v___x_1813_ = l_Lean_Expr_isApp(v___x_1812_);
if (v___x_1813_ == 0)
{
lean_dec_ref(v___x_1812_);
lean_dec(v_goal_1795_);
goto v___jp_1809_;
}
else
{
lean_object* v_arg_1814_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v_arg_1814_ = lean_ctor_get(v___x_1812_, 1);
lean_inc_ref(v_arg_1814_);
v___x_1815_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1812_);
v___x_1816_ = l_Lean_Expr_isApp(v___x_1815_);
if (v___x_1816_ == 0)
{
lean_dec_ref(v___x_1815_);
lean_dec_ref(v_arg_1814_);
lean_dec(v_goal_1795_);
goto v___jp_1809_;
}
else
{
lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1817_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1815_);
v___x_1818_ = l_Lean_Expr_isApp(v___x_1817_);
if (v___x_1818_ == 0)
{
lean_dec_ref(v___x_1817_);
lean_dec_ref(v_arg_1814_);
lean_dec(v_goal_1795_);
goto v___jp_1809_;
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1817_);
v___x_1820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_1821_ = l_Lean_Expr_isConstOf(v___x_1819_, v___x_1820_);
lean_dec_ref(v___x_1819_);
if (v___x_1821_ == 0)
{
lean_dec_ref(v_arg_1814_);
lean_dec(v_goal_1795_);
goto v___jp_1809_;
}
else
{
uint8_t v___x_1822_; 
v___x_1822_ = l_Lean_Expr_isTrue(v_arg_1814_);
if (v___x_1822_ == 0)
{
lean_object* v_backwardRules_1823_; lean_object* v_ofPropPreIntro_1824_; lean_object* v___x_1825_; 
v_backwardRules_1823_ = lean_ctor_get(v_a_1797_, 0);
v_ofPropPreIntro_1824_ = lean_ctor_get(v_backwardRules_1823_, 3);
lean_inc_ref(v_ofPropPreIntro_1824_);
v___x_1825_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_ofPropPreIntro_1824_, v_goal_1795_, v_a_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1834_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1834_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1826_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_a_1835_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1825_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1825_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
lean_dec(v_goal_1795_);
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
return v___x_1844_;
}
}
}
}
}
v___jp_1809_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1810_ = lean_box(0);
v___x_1811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1810_);
return v___x_1811_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_1845_, lean_object* v_pre_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_1845_, v_pre_1846_, v_a_1847_, v_a_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_);
lean_dec(v_a_1857_);
lean_dec_ref(v_a_1856_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec_ref(v_a_1850_);
lean_dec(v_a_1849_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(lean_object* v_goal_1860_, lean_object* v_00_u03b1_1861_, lean_object* v_pre_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = l_Lean_Expr_isProp(v_00_u03b1_1861_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec(v_goal_1860_);
v___x_1876_ = lean_box(0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1879_ = l_Lean_Expr_isAppOf(v_pre_1862_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v_backwardRules_1880_; lean_object* v_propPreIntro_1881_; lean_object* v___x_1882_; 
v_backwardRules_1880_ = lean_ctor_get(v_a_1863_, 0);
v_propPreIntro_1881_ = lean_ctor_get(v_backwardRules_1880_, 2);
lean_inc_ref(v_propPreIntro_1881_);
v___x_1882_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_propPreIntro_1881_, v_goal_1860_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1891_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1885_ = v___x_1882_;
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1882_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1891_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1887_; lean_object* v___x_1889_; 
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_a_1883_);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1887_);
v___x_1889_ = v___x_1885_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
v_a_1892_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1882_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1882_);
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
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec(v_goal_1860_);
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_1902_, lean_object* v_00_u03b1_1903_, lean_object* v_pre_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_1902_, v_00_u03b1_1903_, v_pre_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_);
lean_dec(v_a_1915_);
lean_dec_ref(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec_ref(v_a_1912_);
lean_dec(v_a_1911_);
lean_dec_ref(v_a_1910_);
lean_dec(v_a_1909_);
lean_dec_ref(v_a_1908_);
lean_dec(v_a_1907_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec_ref(v_pre_1904_);
lean_dec_ref(v_00_u03b1_1903_);
return v_res_1917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__0));
v___x_1920_ = l_Lean_stringToMessageData(v___x_1919_);
return v___x_1920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4(void){
_start:
{
uint8_t v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = 0;
v___x_1927_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__3));
v___x_1928_ = l_Lean_MessageData_ofConstName(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__4);
v___x_1930_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__1);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__6));
v___x_1934_ = l_Lean_stringToMessageData(v___x_1933_);
return v___x_1934_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__7);
v___x_1936_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__5);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1935_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(lean_object* v_goal_1938_, lean_object* v_pre_1939_, lean_object* v_target_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_){
_start:
{
lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; uint8_t v___x_1991_; 
lean_inc_ref(v_pre_1939_);
v___x_1991_ = l_Lean_Expr_isTrue(v_pre_1939_);
if (v___x_1991_ == 0)
{
v___y_1954_ = v_a_1946_;
v___y_1955_ = v_a_1947_;
v___y_1956_ = v_a_1948_;
v___y_1957_ = v_a_1949_;
v___y_1958_ = v_a_1950_;
v___y_1959_ = v_a_1951_;
goto v___jp_1953_;
}
else
{
lean_object* v_backwardRules_1992_; lean_object* v_truePreIntro_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
lean_dec_ref(v_pre_1939_);
v_backwardRules_1992_ = lean_ctor_get(v_a_1941_, 0);
v_truePreIntro_1993_ = lean_ctor_get(v_backwardRules_1992_, 4);
v___x_1994_ = lean_box(0);
lean_inc_ref(v_truePreIntro_1993_);
v___x_1995_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_1993_, v_goal_1938_, v___x_1994_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_, v_a_1950_, v_a_1951_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; lean_object* v___x_1998_; uint8_t v_isShared_1999_; uint8_t v_isSharedCheck_2031_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1998_ = v___x_1995_;
v_isShared_1999_ = v_isSharedCheck_2031_;
goto v_resetjp_1997_;
}
else
{
lean_inc(v_a_1996_);
lean_dec(v___x_1995_);
v___x_1998_ = lean_box(0);
v_isShared_1999_ = v_isSharedCheck_2031_;
goto v_resetjp_1997_;
}
v_resetjp_1997_:
{
lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; 
if (lean_obj_tag(v_a_1996_) == 1)
{
lean_object* v_mvarIds_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2030_; 
v_mvarIds_2019_ = lean_ctor_get(v_a_1996_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_a_1996_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2021_ = v_a_1996_;
v_isShared_2022_ = v_isSharedCheck_2030_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_mvarIds_2019_);
lean_dec(v_a_1996_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2030_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
if (lean_obj_tag(v_mvarIds_2019_) == 1)
{
lean_object* v_tail_2023_; 
v_tail_2023_ = lean_ctor_get(v_mvarIds_2019_, 1);
if (lean_obj_tag(v_tail_2023_) == 0)
{
lean_object* v___x_2025_; 
lean_dec_ref(v_target_1940_);
if (v_isShared_2022_ == 0)
{
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_mvarIds_2019_);
v___x_2025_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_1999_ == 0)
{
lean_ctor_set(v___x_1998_, 0, v___x_2025_);
v___x_2027_ = v___x_1998_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_2019_, 2);
lean_del_object(v___x_2021_);
lean_del_object(v___x_1998_);
v___y_2001_ = v_a_1946_;
v___y_2002_ = v_a_1947_;
v___y_2003_ = v_a_1948_;
v___y_2004_ = v_a_1949_;
v___y_2005_ = v_a_1950_;
v___y_2006_ = v_a_1951_;
goto v___jp_2000_;
}
}
else
{
lean_del_object(v___x_2021_);
lean_dec(v_mvarIds_2019_);
lean_del_object(v___x_1998_);
v___y_2001_ = v_a_1946_;
v___y_2002_ = v_a_1947_;
v___y_2003_ = v_a_1948_;
v___y_2004_ = v_a_1949_;
v___y_2005_ = v_a_1950_;
v___y_2006_ = v_a_1951_;
goto v___jp_2000_;
}
}
}
else
{
lean_del_object(v___x_1998_);
lean_dec(v_a_1996_);
v___y_2001_ = v_a_1946_;
v___y_2002_ = v_a_1947_;
v___y_2003_ = v_a_1948_;
v___y_2004_ = v_a_1949_;
v___y_2005_ = v_a_1950_;
v___y_2006_ = v_a_1951_;
goto v___jp_2000_;
}
v___jp_2000_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
v___x_2007_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___closed__8);
v___x_2008_ = l_Lean_indentExpr(v_target_1940_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2009_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_2010_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref(v_target_1940_);
v_a_2032_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_1995_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_1995_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
v___jp_1953_:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceTopAppliedPre_x3f(v_goal_1938_, v_target_1940_, v_pre_1939_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1963_; uint8_t v_isShared_1964_; uint8_t v_isSharedCheck_1982_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1963_ = v___x_1960_;
v_isShared_1964_ = v_isSharedCheck_1982_;
goto v_resetjp_1962_;
}
else
{
lean_inc(v_a_1961_);
lean_dec(v___x_1960_);
v___x_1963_ = lean_box(0);
v_isShared_1964_ = v_isSharedCheck_1982_;
goto v_resetjp_1962_;
}
v_resetjp_1962_:
{
if (lean_obj_tag(v_a_1961_) == 1)
{
lean_object* v_val_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1977_; 
v_val_1965_ = lean_ctor_get(v_a_1961_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1961_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1967_ = v_a_1961_;
v_isShared_1968_ = v_isSharedCheck_1977_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_val_1965_);
lean_dec(v_a_1961_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1977_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1970_, 0, v_val_1965_);
lean_ctor_set(v___x_1970_, 1, v___x_1969_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1970_);
v___x_1972_ = v___x_1967_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1974_; 
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1972_);
v___x_1974_ = v___x_1963_;
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
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1980_; 
lean_dec(v_a_1961_);
v___x_1978_ = lean_box(0);
if (v_isShared_1964_ == 0)
{
lean_ctor_set(v___x_1963_, 0, v___x_1978_);
v___x_1980_ = v___x_1963_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v___x_1978_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_a_1983_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___x_1960_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1960_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_a_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f___boxed(lean_object* v_goal_2040_, lean_object* v_pre_2041_, lean_object* v_target_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2040_, v_pre_2041_, v_target_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_, v_a_2053_);
lean_dec(v_a_2053_);
lean_dec_ref(v_a_2052_);
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2050_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object* v_scope_2056_, lean_object* v_goal_2057_, lean_object* v_00_u03b1_2058_, lean_object* v_pre_2059_, lean_object* v_target_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v_g_2074_; lean_object* v_g_2081_; lean_object* v_h_2082_; lean_object* v___x_2100_; 
lean_inc_ref(v_pre_2059_);
lean_inc(v_goal_2057_);
v___x_2100_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_2057_, v_pre_2059_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref_known(v___x_2100_, 1);
if (lean_obj_tag(v_a_2101_) == 1)
{
lean_object* v_val_2102_; 
lean_dec_ref(v_target_2060_);
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
v_val_2102_ = lean_ctor_get(v_a_2101_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v_a_2101_, 1);
v_g_2074_ = v_val_2102_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2103_; 
lean_dec(v_a_2101_);
lean_inc_ref(v_pre_2059_);
lean_inc(v_goal_2057_);
v___x_2103_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_2057_, v_pre_2059_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v_a_2104_; 
v_a_2104_ = lean_ctor_get(v___x_2103_, 0);
lean_inc(v_a_2104_);
lean_dec_ref_known(v___x_2103_, 1);
if (lean_obj_tag(v_a_2104_) == 1)
{
lean_object* v_val_2105_; lean_object* v_fst_2106_; lean_object* v_snd_2107_; 
lean_dec_ref(v_target_2060_);
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
v_val_2105_ = lean_ctor_get(v_a_2104_, 0);
lean_inc(v_val_2105_);
lean_dec_ref_known(v_a_2104_, 1);
v_fst_2106_ = lean_ctor_get(v_val_2105_, 0);
lean_inc(v_fst_2106_);
v_snd_2107_ = lean_ctor_get(v_val_2105_, 1);
lean_inc(v_snd_2107_);
lean_dec(v_val_2105_);
v_g_2081_ = v_fst_2106_;
v_h_2082_ = v_snd_2107_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2108_; 
lean_dec(v_a_2104_);
lean_inc(v_goal_2057_);
v___x_2108_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_2057_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
if (lean_obj_tag(v_a_2109_) == 1)
{
lean_object* v_val_2110_; 
lean_dec_ref(v_target_2060_);
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
v_val_2110_ = lean_ctor_get(v_a_2109_, 0);
lean_inc(v_val_2110_);
lean_dec_ref_known(v_a_2109_, 1);
v_g_2074_ = v_val_2110_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2111_; 
lean_dec(v_a_2109_);
lean_inc_ref(v_pre_2059_);
lean_inc(v_goal_2057_);
v___x_2111_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePreToTop_x3f(v_goal_2057_, v_pre_2059_, v_target_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2149_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2149_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2149_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
if (lean_obj_tag(v_a_2112_) == 1)
{
lean_object* v_val_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2127_; 
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
v_val_2116_ = lean_ctor_get(v_a_2112_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_a_2112_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2118_ = v_a_2112_;
v_isShared_2119_ = v_isSharedCheck_2127_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_val_2116_);
lean_dec(v_a_2112_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2127_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v_scope_2056_);
lean_ctor_set(v___x_2120_, 1, v_val_2116_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2122_);
v___x_2124_ = v___x_2114_;
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
}
else
{
lean_object* v___x_2128_; 
lean_del_object(v___x_2114_);
lean_dec(v_a_2112_);
v___x_2128_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_2057_, v_00_u03b1_2058_, v_pre_2059_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_, v_a_2071_);
lean_dec_ref(v_pre_2059_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2140_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2131_ = v___x_2128_;
v_isShared_2132_ = v_isSharedCheck_2140_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2128_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2140_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
if (lean_obj_tag(v_a_2129_) == 1)
{
lean_object* v_val_2133_; lean_object* v_fst_2134_; lean_object* v_snd_2135_; 
lean_del_object(v___x_2131_);
v_val_2133_ = lean_ctor_get(v_a_2129_, 0);
lean_inc(v_val_2133_);
lean_dec_ref_known(v_a_2129_, 1);
v_fst_2134_ = lean_ctor_get(v_val_2133_, 0);
lean_inc(v_fst_2134_);
v_snd_2135_ = lean_ctor_get(v_val_2133_, 1);
lean_inc(v_snd_2135_);
lean_dec(v_val_2133_);
v_g_2081_ = v_fst_2134_;
v_h_2082_ = v_snd_2135_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2136_; lean_object* v___x_2138_; 
lean_dec(v_a_2129_);
lean_dec_ref(v_scope_2056_);
v___x_2136_ = lean_box(0);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2136_);
v___x_2138_ = v___x_2131_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2136_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref(v_scope_2056_);
v_a_2141_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2128_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2128_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
lean_dec_ref(v_scope_2056_);
v_a_2150_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2111_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2111_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_dec_ref(v_target_2060_);
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
lean_dec_ref(v_scope_2056_);
v_a_2158_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2108_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2108_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec_ref(v_target_2060_);
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
lean_dec_ref(v_scope_2056_);
v_a_2166_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2103_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2103_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v_target_2060_);
lean_dec_ref(v_pre_2059_);
lean_dec(v_goal_2057_);
lean_dec_ref(v_scope_2056_);
v_a_2174_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2100_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2100_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
v___jp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2075_ = lean_box(0);
v___x_2076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2076_, 0, v_g_2074_);
lean_ctor_set(v___x_2076_, 1, v___x_2075_);
v___x_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2077_, 0, v_scope_2056_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
v___jp_2080_:
{
lean_object* v_specs_2083_; lean_object* v_jps_2084_; lean_object* v_nextDeclIdx_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2098_; 
v_specs_2083_ = lean_ctor_get(v_scope_2056_, 0);
v_jps_2084_ = lean_ctor_get(v_scope_2056_, 1);
v_nextDeclIdx_2085_ = lean_ctor_get(v_scope_2056_, 3);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_scope_2056_);
if (v_isSharedCheck_2098_ == 0)
{
lean_object* v_unused_2099_; 
v_unused_2099_ = lean_ctor_get(v_scope_2056_, 2);
lean_dec(v_unused_2099_);
v___x_2087_ = v_scope_2056_;
v_isShared_2088_ = v_isSharedCheck_2098_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_nextDeclIdx_2085_);
lean_inc(v_jps_2084_);
lean_inc(v_specs_2083_);
lean_dec(v_scope_2056_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2098_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_h_2082_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 2, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_specs_2083_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_jps_2084_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v_nextDeclIdx_2085_);
v___x_2091_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2092_ = lean_box(0);
v___x_2093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2093_, 0, v_g_2081_);
lean_ctor_set(v___x_2093_, 1, v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2091_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
return v___x_2096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2182_ = _args[0];
lean_object* v_goal_2183_ = _args[1];
lean_object* v_00_u03b1_2184_ = _args[2];
lean_object* v_pre_2185_ = _args[3];
lean_object* v_target_2186_ = _args[4];
lean_object* v_a_2187_ = _args[5];
lean_object* v_a_2188_ = _args[6];
lean_object* v_a_2189_ = _args[7];
lean_object* v_a_2190_ = _args[8];
lean_object* v_a_2191_ = _args[9];
lean_object* v_a_2192_ = _args[10];
lean_object* v_a_2193_ = _args[11];
lean_object* v_a_2194_ = _args[12];
lean_object* v_a_2195_ = _args[13];
lean_object* v_a_2196_ = _args[14];
lean_object* v_a_2197_ = _args[15];
lean_object* v_a_2198_ = _args[16];
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_2182_, v_goal_2183_, v_00_u03b1_2184_, v_pre_2185_, v_target_2186_, v_a_2187_, v_a_2188_, v_a_2189_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
lean_dec(v_a_2191_);
lean_dec_ref(v_a_2190_);
lean_dec(v_a_2189_);
lean_dec(v_a_2188_);
lean_dec_ref(v_a_2187_);
lean_dec_ref(v_00_u03b1_2184_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2200_, lean_object* v_a_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___y_2210_; lean_object* v___x_2213_; uint8_t v_debug_2214_; 
v___x_2213_ = lean_st_ref_get(v___y_2203_);
v_debug_2214_ = lean_ctor_get_uint8(v___x_2213_, sizeof(void*)*11);
lean_dec(v___x_2213_);
if (v_debug_2214_ == 0)
{
v___y_2210_ = v___y_2203_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2215_; 
lean_inc_ref(v_f_2200_);
v___x_2215_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2200_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v___x_2216_; 
lean_dec_ref_known(v___x_2215_, 1);
lean_inc_ref(v_a_2201_);
v___x_2216_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_dec_ref_known(v___x_2216_, 1);
v___y_2210_ = v___y_2203_;
goto v___jp_2209_;
}
else
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2224_; 
lean_dec_ref(v_a_2201_);
lean_dec_ref(v_f_2200_);
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2224_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v___x_2222_; 
if (v_isShared_2220_ == 0)
{
v___x_2222_ = v___x_2219_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_a_2217_);
v___x_2222_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
return v___x_2222_;
}
}
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_a_2201_);
lean_dec_ref(v_f_2200_);
v_a_2225_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2215_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2215_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
v___jp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2211_ = l_Lean_Expr_app___override(v_f_2200_, v_a_2201_);
v___x_2212_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2211_, v___y_2210_);
return v___x_2212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2233_, lean_object* v_a_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2233_, v_a_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object* v_args_2243_, lean_object* v_endIdx_2244_, lean_object* v_b_2245_, lean_object* v_i_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_nat_dec_le(v_endIdx_2244_, v_i_2246_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = l_Lean_instInhabitedExpr;
v___x_2261_ = lean_array_get_borrowed(v___x_2260_, v_args_2243_, v_i_2246_);
lean_inc(v___x_2261_);
v___x_2262_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2245_, v___x_2261_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = lean_unsigned_to_nat(1u);
v___x_2265_ = lean_nat_add(v_i_2246_, v___x_2264_);
lean_dec(v_i_2246_);
v_b_2245_ = v_a_2263_;
v_i_2246_ = v___x_2265_;
goto _start;
}
else
{
lean_dec(v_i_2246_);
return v___x_2262_;
}
}
else
{
lean_object* v___x_2267_; 
lean_dec(v_i_2246_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_b_2245_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object* v_args_2268_, lean_object* v_endIdx_2269_, lean_object* v_b_2270_, lean_object* v_i_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2268_, v_endIdx_2269_, v_b_2270_, v_i_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v_endIdx_2269_);
lean_dec_ref(v_args_2268_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object* v_f_2285_, lean_object* v_args_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2299_ = lean_unsigned_to_nat(0u);
v___x_2300_ = lean_array_get_size(v_args_2286_);
v___x_2301_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2286_, v___x_2300_, v_f_2285_, v___x_2299_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object* v_f_2302_, lean_object* v_args_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_2302_, v_args_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_args_2303_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_2317_, lean_object* v_info_2318_, lean_object* v_prog_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_head_2332_; lean_object* v_args_2333_; lean_object* v_excessArgs_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v_head_2332_ = lean_ctor_get(v_info_2318_, 0);
lean_inc_ref(v_head_2332_);
v_args_2333_ = lean_ctor_get(v_info_2318_, 1);
lean_inc_ref(v_args_2333_);
v_excessArgs_2334_ = lean_ctor_get(v_info_2318_, 2);
lean_inc_ref(v_excessArgs_2334_);
lean_dec_ref(v_info_2318_);
v___x_2335_ = lean_unsigned_to_nat(7u);
v___x_2336_ = lean_array_set(v_args_2333_, v___x_2335_, v_prog_2319_);
v___x_2337_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2332_, v___x_2336_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec_ref(v___x_2336_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2338_, v_excessArgs_2334_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec_ref(v_excessArgs_2334_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
lean_inc(v_goal_2317_);
v___x_2341_ = l_Lean_MVarId_getType(v_goal_2317_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v_dummy_2343_; lean_object* v_nargs_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc_n(v_a_2342_, 2);
lean_dec_ref_known(v___x_2341_, 1);
v_dummy_2343_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_2344_ = l_Lean_Expr_getAppNumArgs(v_a_2342_);
lean_inc(v_nargs_2344_);
v___x_2345_ = lean_mk_array(v_nargs_2344_, v_dummy_2343_);
v___x_2346_ = lean_unsigned_to_nat(1u);
v___x_2347_ = lean_nat_sub(v_nargs_2344_, v___x_2346_);
lean_dec(v_nargs_2344_);
v___x_2348_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2342_, v___x_2345_, v___x_2347_);
v___x_2349_ = l_Lean_Expr_getAppFn(v_a_2342_);
lean_dec(v_a_2342_);
v___x_2350_ = lean_array_get_size(v___x_2348_);
v___x_2351_ = lean_nat_sub(v___x_2350_, v___x_2346_);
v___x_2352_ = lean_array_set(v___x_2348_, v___x_2351_, v_a_2340_);
lean_dec(v___x_2351_);
v___x_2353_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2349_, v___x_2352_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
lean_dec_ref(v___x_2352_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc(v_a_2354_);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_2317_, v_a_2354_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2355_;
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec(v_goal_2317_);
v_a_2356_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2353_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2353_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2340_);
lean_dec(v_goal_2317_);
v_a_2364_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2341_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2341_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_goal_2317_);
v_a_2372_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2339_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2339_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v_excessArgs_2334_);
lean_dec(v_goal_2317_);
v_a_2380_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2337_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2337_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2388_, lean_object* v_info_2389_, lean_object* v_prog_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2388_, v_info_2389_, v_prog_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_, v_a_2399_, v_a_2400_, v_a_2401_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
lean_dec(v_a_2399_);
lean_dec_ref(v_a_2398_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
lean_dec(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(lean_object* v_f_2404_, lean_object* v_a_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
lean_object* v___x_2418_; 
v___x_2418_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2404_, v_a_2405_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2419_, lean_object* v_a_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(v_f_2419_, v_a_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
lean_dec(v___y_2431_);
lean_dec_ref(v___y_2430_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(lean_object* v_goal_2434_, lean_object* v_info_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2435_);
if (lean_obj_tag(v___x_2448_) == 10)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = l_Lean_Expr_consumeMData(v___x_2448_);
lean_dec_ref_known(v___x_2448_, 2);
v___x_2450_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2434_, v_info_2435_, v___x_2449_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2459_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2459_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v_a_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v_a_2460_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2450_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2450_);
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
else
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_dec_ref(v___x_2448_);
lean_dec_ref(v_info_2435_);
lean_dec(v_goal_2434_);
v___x_2468_ = lean_box(0);
v___x_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f___boxed(lean_object* v_goal_2470_, lean_object* v_info_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_, lean_object* v_a_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_2470_, v_info_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
lean_dec(v_a_2482_);
lean_dec_ref(v_a_2481_);
lean_dec(v_a_2480_);
lean_dec_ref(v_a_2479_);
lean_dec(v_a_2478_);
lean_dec_ref(v_a_2477_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2485_, lean_object* v_start_2486_, lean_object* v_b_2487_, lean_object* v_i_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
uint8_t v___x_2496_; 
v___x_2496_ = lean_nat_dec_le(v_i_2488_, v_start_2486_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v_i_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v_i_2498_ = lean_nat_sub(v_i_2488_, v___x_2497_);
lean_dec(v_i_2488_);
v___x_2499_ = l_Lean_instInhabitedExpr;
v___x_2500_ = lean_array_get_borrowed(v___x_2499_, v_revArgs_2485_, v_i_2498_);
lean_inc(v___x_2500_);
v___x_2501_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2487_, v___x_2500_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v_b_2487_ = v_a_2502_;
v_i_2488_ = v_i_2498_;
goto _start;
}
else
{
lean_dec(v_i_2498_);
return v___x_2501_;
}
}
else
{
lean_object* v___x_2504_; 
lean_dec(v_i_2488_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v_b_2487_);
return v___x_2504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2505_, lean_object* v_start_2506_, lean_object* v_b_2507_, lean_object* v_i_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2505_, v_start_2506_, v_b_2507_, v_i_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v_start_2506_);
lean_dec_ref(v_revArgs_2505_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2517_, lean_object* v_revArgs_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_unsigned_to_nat(0u);
v___x_2532_ = lean_array_get_size(v_revArgs_2518_);
v___x_2533_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2518_, v___x_2531_, v_f_2517_, v___x_2532_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_2534_, lean_object* v_revArgs_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_f_2534_, v_revArgs_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_);
lean_dec(v___y_2546_);
lean_dec_ref(v___y_2545_);
lean_dec(v___y_2544_);
lean_dec_ref(v___y_2543_);
lean_dec(v___y_2542_);
lean_dec_ref(v___y_2541_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec(v___y_2537_);
lean_dec_ref(v___y_2536_);
lean_dec_ref(v_revArgs_2535_);
return v_res_2548_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0));
v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2553_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2));
v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object* v_goal_2555_, lean_object* v_info_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2569_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2556_);
v___x_2570_ = l_Lean_Expr_getAppFn(v___x_2569_);
if (lean_obj_tag(v___x_2570_) == 8)
{
lean_object* v_declName_2571_; lean_object* v_type_2572_; lean_object* v_value_2573_; lean_object* v_body_2574_; uint8_t v_nondep_2575_; lean_object* v___x_2576_; 
v_declName_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_n(v_declName_2571_, 2);
v_type_2572_ = lean_ctor_get(v___x_2570_, 1);
lean_inc_ref(v_type_2572_);
v_value_2573_ = lean_ctor_get(v___x_2570_, 2);
lean_inc_ref(v_value_2573_);
v_body_2574_ = lean_ctor_get(v___x_2570_, 3);
lean_inc_ref(v_body_2574_);
v_nondep_2575_ = lean_ctor_get_uint8(v___x_2570_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_2570_, 4);
v___x_2576_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_2571_, v_value_2573_, v_a_2557_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_appArgs_2579_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; uint8_t v___x_2633_; 
lean_dec_ref_known(v___x_2576_, 1);
v___x_2577_ = l_Lean_Expr_getAppNumArgs(v___x_2569_);
v___x_2578_ = lean_mk_empty_array_with_capacity(v___x_2577_);
lean_dec(v___x_2577_);
v_appArgs_2579_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2569_, v___x_2578_);
v___x_2633_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_2573_);
if (v___x_2633_ == 0)
{
lean_object* v_options_2634_; lean_object* v_inheritedTraceOptions_2635_; uint8_t v_hasTrace_2636_; uint8_t v___x_2637_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; 
v_options_2634_ = lean_ctor_get(v_a_2566_, 2);
v_inheritedTraceOptions_2635_ = lean_ctor_get(v_a_2566_, 13);
v_hasTrace_2636_ = lean_ctor_get_uint8(v_options_2634_, sizeof(void*)*1);
v___x_2637_ = 1;
if (v_hasTrace_2636_ == 0)
{
v___y_2639_ = v_a_2557_;
v___y_2640_ = v_a_2558_;
v___y_2641_ = v_a_2559_;
v___y_2642_ = v_a_2560_;
v___y_2643_ = v_a_2561_;
v___y_2644_ = v_a_2562_;
v___y_2645_ = v_a_2563_;
v___y_2646_ = v_a_2564_;
v___y_2647_ = v_a_2565_;
v___y_2648_ = v_a_2566_;
v___y_2649_ = v_a_2567_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2749_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2635_, v_options_2634_, v___x_2749_);
if (v___x_2750_ == 0)
{
v___y_2639_ = v_a_2557_;
v___y_2640_ = v_a_2558_;
v___y_2641_ = v_a_2559_;
v___y_2642_ = v_a_2560_;
v___y_2643_ = v_a_2561_;
v___y_2644_ = v_a_2562_;
v___y_2645_ = v_a_2563_;
v___y_2646_ = v_a_2564_;
v___y_2647_ = v_a_2565_;
v___y_2648_ = v_a_2566_;
v___y_2649_ = v_a_2567_;
goto v___jp_2638_;
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2751_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_2571_);
v___x_2752_ = l_Lean_MessageData_ofName(v_declName_2571_);
v___x_2753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2751_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2748_, v___x_2753_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_dec_ref_known(v___x_2754_, 1);
v___y_2639_ = v_a_2557_;
v___y_2640_ = v_a_2558_;
v___y_2641_ = v_a_2559_;
v___y_2642_ = v_a_2560_;
v___y_2643_ = v_a_2561_;
v___y_2644_ = v_a_2562_;
v___y_2645_ = v_a_2563_;
v___y_2646_ = v_a_2564_;
v___y_2647_ = v_a_2565_;
v___y_2648_ = v_a_2566_;
v___y_2649_ = v_a_2567_;
goto v___jp_2638_;
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2762_; 
lean_dec_ref(v_appArgs_2579_);
lean_dec_ref(v_body_2574_);
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2762_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
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
v___jp_2638_:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_body_2574_, v_appArgs_2579_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v_appArgs_2579_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v_head_2652_; lean_object* v_args_2653_; lean_object* v_excessArgs_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v_head_2652_ = lean_ctor_get(v_info_2556_, 0);
lean_inc_ref(v_head_2652_);
v_args_2653_ = lean_ctor_get(v_info_2556_, 1);
lean_inc_ref(v_args_2653_);
v_excessArgs_2654_ = lean_ctor_get(v_info_2556_, 2);
lean_inc_ref(v_excessArgs_2654_);
lean_dec_ref(v_info_2556_);
v___x_2655_ = lean_unsigned_to_nat(7u);
v___x_2656_ = lean_array_set(v_args_2653_, v___x_2655_, v_a_2651_);
v___x_2657_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2652_, v___x_2656_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v___x_2656_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2658_, v_excessArgs_2654_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v_excessArgs_2654_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
lean_inc(v_goal_2555_);
v___x_2661_ = l_Lean_MVarId_getType(v_goal_2555_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v_dummy_2663_; lean_object* v_nargs_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_n(v_a_2662_, 2);
lean_dec_ref_known(v___x_2661_, 1);
v_dummy_2663_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_2664_ = l_Lean_Expr_getAppNumArgs(v_a_2662_);
lean_inc(v_nargs_2664_);
v___x_2665_ = lean_mk_array(v_nargs_2664_, v_dummy_2663_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_sub(v_nargs_2664_, v___x_2666_);
lean_dec(v_nargs_2664_);
v___x_2668_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2662_, v___x_2665_, v___x_2667_);
v___x_2669_ = l_Lean_Expr_getAppFn(v_a_2662_);
lean_dec(v_a_2662_);
v___x_2670_ = lean_array_get_size(v___x_2668_);
v___x_2671_ = lean_nat_sub(v___x_2670_, v___x_2666_);
v___x_2672_ = lean_array_set(v___x_2668_, v___x_2671_, v_a_2660_);
lean_dec(v___x_2671_);
v___x_2673_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2669_, v___x_2672_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
lean_dec_ref(v___x_2672_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = l_Lean_Expr_letE___override(v_declName_2571_, v_type_2572_, v_value_2573_, v_a_2674_, v_nondep_2575_);
v___x_2676_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_2555_, v___x_2675_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2));
v___x_2679_ = l_Lean_Meta_Sym_intros(v_a_2677_, v___x_2678_, v___x_2637_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2691_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2682_ = v___x_2679_;
v_isShared_2683_ = v_isSharedCheck_2691_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_a_2680_);
lean_dec(v___x_2679_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2691_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
if (lean_obj_tag(v_a_2680_) == 1)
{
lean_object* v_mvarId_2684_; lean_object* v___x_2685_; lean_object* v___x_2687_; 
v_mvarId_2684_ = lean_ctor_get(v_a_2680_, 1);
lean_inc(v_mvarId_2684_);
lean_dec_ref_known(v_a_2680_, 2);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v_mvarId_2684_);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 0, v___x_2685_);
v___x_2687_ = v___x_2682_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
else
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
lean_del_object(v___x_2682_);
lean_dec(v_a_2680_);
v___x_2689_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1);
v___x_2690_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2689_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2690_;
}
}
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_a_2692_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2679_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2679_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v_a_2700_; lean_object* v___x_2702_; uint8_t v_isShared_2703_; uint8_t v_isSharedCheck_2707_; 
v_a_2700_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2702_ = v___x_2676_;
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
else
{
lean_inc(v_a_2700_);
lean_dec(v___x_2676_);
v___x_2702_ = lean_box(0);
v_isShared_2703_ = v_isSharedCheck_2707_;
goto v_resetjp_2701_;
}
v_resetjp_2701_:
{
lean_object* v___x_2705_; 
if (v_isShared_2703_ == 0)
{
v___x_2705_ = v___x_2702_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v_a_2700_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2715_; 
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec(v_goal_2555_);
v_a_2708_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2715_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2715_ == 0)
{
v___x_2710_ = v___x_2673_;
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_a_2708_);
lean_dec(v___x_2673_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2715_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2713_; 
if (v_isShared_2711_ == 0)
{
v___x_2713_ = v___x_2710_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2708_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec(v_a_2660_);
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec(v_goal_2555_);
v_a_2716_ = lean_ctor_get(v___x_2661_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2661_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2661_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec(v_goal_2555_);
v_a_2724_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2659_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2659_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v_excessArgs_2654_);
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec(v_goal_2555_);
v_a_2732_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2657_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2657_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v_a_2740_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2650_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2650_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
else
{
lean_object* v_options_2763_; uint8_t v_hasTrace_2764_; 
lean_dec_ref(v_type_2572_);
v_options_2763_ = lean_ctor_get(v_a_2566_, 2);
v_hasTrace_2764_ = lean_ctor_get_uint8(v_options_2763_, sizeof(void*)*1);
if (v_hasTrace_2764_ == 0)
{
lean_dec(v_declName_2571_);
v___y_2581_ = v_a_2557_;
v___y_2582_ = v_a_2558_;
v___y_2583_ = v_a_2559_;
v___y_2584_ = v_a_2560_;
v___y_2585_ = v_a_2561_;
v___y_2586_ = v_a_2562_;
v___y_2587_ = v_a_2563_;
v___y_2588_ = v_a_2564_;
v___y_2589_ = v_a_2565_;
v___y_2590_ = v_a_2566_;
v___y_2591_ = v_a_2567_;
goto v___jp_2580_;
}
else
{
lean_object* v_inheritedTraceOptions_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_inheritedTraceOptions_2765_ = lean_ctor_get(v_a_2566_, 13);
v___x_2766_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2767_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2768_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2765_, v_options_2763_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_dec(v_declName_2571_);
v___y_2581_ = v_a_2557_;
v___y_2582_ = v_a_2558_;
v___y_2583_ = v_a_2559_;
v___y_2584_ = v_a_2560_;
v___y_2585_ = v_a_2561_;
v___y_2586_ = v_a_2562_;
v___y_2587_ = v_a_2563_;
v___y_2588_ = v_a_2564_;
v___y_2589_ = v_a_2565_;
v___y_2590_ = v_a_2566_;
v___y_2591_ = v_a_2567_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2769_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_2770_ = l_Lean_MessageData_ofName(v_declName_2571_);
v___x_2771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2769_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2766_, v___x_2771_, v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_dec_ref_known(v___x_2772_, 1);
v___y_2581_ = v_a_2557_;
v___y_2582_ = v_a_2558_;
v___y_2583_ = v_a_2559_;
v___y_2584_ = v_a_2560_;
v___y_2585_ = v_a_2561_;
v___y_2586_ = v_a_2562_;
v___y_2587_ = v_a_2563_;
v___y_2588_ = v_a_2564_;
v___y_2589_ = v_a_2565_;
v___y_2590_ = v_a_2566_;
v___y_2591_ = v_a_2567_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2780_; 
lean_dec_ref(v_appArgs_2579_);
lean_dec_ref(v_body_2574_);
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2780_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2780_ == 0)
{
v___x_2775_ = v___x_2772_;
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v___x_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2780_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
if (v_isShared_2776_ == 0)
{
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
}
}
v___jp_2580_:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2592_ = lean_unsigned_to_nat(1u);
v___x_2593_ = lean_mk_empty_array_with_capacity(v___x_2592_);
v___x_2594_ = lean_array_push(v___x_2593_, v_value_2573_);
v___x_2595_ = l_Lean_Meta_Sym_instantiateRevBetaS(v_body_2574_, v___x_2594_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_a_2596_, v_appArgs_2579_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec_ref(v_appArgs_2579_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2555_, v_info_2556_, v_a_2598_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2608_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v___x_2604_; lean_object* v___x_2606_; 
v___x_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2600_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v___x_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2599_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2599_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v_a_2617_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2597_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2597_);
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
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v_appArgs_2579_);
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v_a_2625_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2595_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2595_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
else
{
lean_object* v_a_2781_; lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
lean_dec_ref(v_body_2574_);
lean_dec_ref(v_value_2573_);
lean_dec_ref(v_type_2572_);
lean_dec(v_declName_2571_);
lean_dec_ref(v___x_2569_);
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v_a_2781_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2783_ = v___x_2576_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_inc(v_a_2781_);
lean_dec(v___x_2576_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2781_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
lean_dec_ref(v___x_2570_);
lean_dec_ref(v___x_2569_);
lean_dec_ref(v_info_2556_);
lean_dec(v_goal_2555_);
v___x_2789_ = lean_box(0);
v___x_2790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
return v___x_2790_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object* v_goal_2791_, lean_object* v_info_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_2791_, v_info_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
lean_dec(v_a_2803_);
lean_dec_ref(v_a_2802_);
lean_dec(v_a_2801_);
lean_dec_ref(v_a_2800_);
lean_dec(v_a_2799_);
lean_dec_ref(v_a_2798_);
lean_dec(v_a_2797_);
lean_dec_ref(v_a_2796_);
lean_dec(v_a_2795_);
lean_dec(v_a_2794_);
lean_dec_ref(v_a_2793_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_2806_, lean_object* v_start_2807_, lean_object* v_b_2808_, lean_object* v_i_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2806_, v_start_2807_, v_b_2808_, v_i_2809_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_2823_, lean_object* v_start_2824_, lean_object* v_b_2825_, lean_object* v_i_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_2823_, v_start_2824_, v_b_2825_, v_i_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
lean_dec(v___y_2835_);
lean_dec_ref(v___y_2834_);
lean_dec(v___y_2833_);
lean_dec_ref(v___y_2832_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v_start_2824_);
lean_dec_ref(v_revArgs_2823_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_2840_, lean_object* v_b_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
if (lean_obj_tag(v_as_x27_2840_) == 0)
{
lean_object* v___x_2851_; 
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v_b_2841_);
return v___x_2851_;
}
else
{
lean_object* v_head_2852_; lean_object* v_tail_2853_; lean_object* v___x_2854_; 
v_head_2852_ = lean_ctor_get(v_as_x27_2840_, 0);
v_tail_2853_ = lean_ctor_get(v_as_x27_2840_, 1);
lean_inc(v_head_2852_);
v___x_2854_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_head_2852_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc(v_a_2855_);
lean_dec_ref_known(v___x_2854_, 1);
switch(lean_obj_tag(v_a_2855_))
{
case 0:
{
lean_object* v___x_2856_; 
lean_inc(v_head_2852_);
v___x_2856_ = lean_array_push(v_b_2841_, v_head_2852_);
v_as_x27_2840_ = v_tail_2853_;
v_b_2841_ = v___x_2856_;
goto _start;
}
case 1:
{
v_as_x27_2840_ = v_tail_2853_;
goto _start;
}
default: 
{
lean_object* v_mvarId_2859_; lean_object* v___x_2860_; 
v_mvarId_2859_ = lean_ctor_get(v_a_2855_, 0);
lean_inc(v_mvarId_2859_);
lean_dec_ref_known(v_a_2855_, 1);
v___x_2860_ = lean_array_push(v_b_2841_, v_mvarId_2859_);
v_as_x27_2840_ = v_tail_2853_;
v_b_2841_ = v___x_2860_;
goto _start;
}
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v_b_2841_);
v_a_2862_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2854_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2854_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_2870_, lean_object* v_b_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_2870_, v_b_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
lean_dec(v_as_x27_2870_);
return v_res_2881_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0));
v___x_2884_ = l_Lean_stringToMessageData(v___x_2883_);
return v___x_2884_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2));
v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
return v___x_2887_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4(void){
_start:
{
uint8_t v___x_2888_; uint64_t v___x_2889_; 
v___x_2888_ = 2;
v___x_2889_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object* v_goal_2890_, lean_object* v_info_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2891_);
lean_inc_ref(v___x_2904_);
v___x_2905_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_2904_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_3079_; 
v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_2908_ = v___x_2905_;
v_isShared_2909_ = v_isSharedCheck_3079_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2905_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_3079_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
if (lean_obj_tag(v_a_2906_) == 1)
{
lean_object* v_val_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_3074_; 
lean_del_object(v___x_2908_);
v_val_2910_ = lean_ctor_get(v_a_2906_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_a_2906_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_2912_ = v_a_2906_;
v_isShared_2913_ = v_isSharedCheck_3074_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_val_2910_);
lean_dec(v_a_2906_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_3074_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___y_2915_; lean_object* v___y_2916_; lean_object* v___y_2917_; lean_object* v___y_2918_; lean_object* v___y_2919_; lean_object* v___y_2920_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; 
if (lean_obj_tag(v_val_2910_) == 2)
{
lean_object* v___x_2982_; uint8_t v_foApprox_2983_; uint8_t v_ctxApprox_2984_; uint8_t v_quasiPatternApprox_2985_; uint8_t v_constApprox_2986_; uint8_t v_isDefEqStuckEx_2987_; uint8_t v_unificationHints_2988_; uint8_t v_proofIrrelevance_2989_; uint8_t v_assignSyntheticOpaque_2990_; uint8_t v_offsetCnstrs_2991_; uint8_t v_etaStruct_2992_; uint8_t v_univApprox_2993_; uint8_t v_iota_2994_; uint8_t v_beta_2995_; uint8_t v_proj_2996_; uint8_t v_zeta_2997_; uint8_t v_zetaDelta_2998_; uint8_t v_zetaUnused_2999_; uint8_t v_zetaHave_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3073_; 
v___x_2982_ = l_Lean_Meta_Context_config(v_a_2899_);
v_foApprox_2983_ = lean_ctor_get_uint8(v___x_2982_, 0);
v_ctxApprox_2984_ = lean_ctor_get_uint8(v___x_2982_, 1);
v_quasiPatternApprox_2985_ = lean_ctor_get_uint8(v___x_2982_, 2);
v_constApprox_2986_ = lean_ctor_get_uint8(v___x_2982_, 3);
v_isDefEqStuckEx_2987_ = lean_ctor_get_uint8(v___x_2982_, 4);
v_unificationHints_2988_ = lean_ctor_get_uint8(v___x_2982_, 5);
v_proofIrrelevance_2989_ = lean_ctor_get_uint8(v___x_2982_, 6);
v_assignSyntheticOpaque_2990_ = lean_ctor_get_uint8(v___x_2982_, 7);
v_offsetCnstrs_2991_ = lean_ctor_get_uint8(v___x_2982_, 8);
v_etaStruct_2992_ = lean_ctor_get_uint8(v___x_2982_, 10);
v_univApprox_2993_ = lean_ctor_get_uint8(v___x_2982_, 11);
v_iota_2994_ = lean_ctor_get_uint8(v___x_2982_, 12);
v_beta_2995_ = lean_ctor_get_uint8(v___x_2982_, 13);
v_proj_2996_ = lean_ctor_get_uint8(v___x_2982_, 14);
v_zeta_2997_ = lean_ctor_get_uint8(v___x_2982_, 15);
v_zetaDelta_2998_ = lean_ctor_get_uint8(v___x_2982_, 16);
v_zetaUnused_2999_ = lean_ctor_get_uint8(v___x_2982_, 17);
v_zetaHave_3000_ = lean_ctor_get_uint8(v___x_2982_, 18);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3002_ = v___x_2982_;
v_isShared_3003_ = v_isSharedCheck_3073_;
goto v_resetjp_3001_;
}
else
{
lean_dec(v___x_2982_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3073_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
uint8_t v_trackZetaDelta_3004_; lean_object* v_zetaDeltaSet_3005_; lean_object* v_lctx_3006_; lean_object* v_localInstances_3007_; lean_object* v_defEqCtx_x3f_3008_; lean_object* v_synthPendingDepth_3009_; lean_object* v_canUnfold_x3f_3010_; uint8_t v_univApprox_3011_; uint8_t v_inTypeClassResolution_3012_; uint8_t v_cacheInferType_3013_; uint8_t v___x_3014_; lean_object* v_config_3016_; 
v_trackZetaDelta_3004_ = lean_ctor_get_uint8(v_a_2899_, sizeof(void*)*7);
v_zetaDeltaSet_3005_ = lean_ctor_get(v_a_2899_, 1);
v_lctx_3006_ = lean_ctor_get(v_a_2899_, 2);
v_localInstances_3007_ = lean_ctor_get(v_a_2899_, 3);
v_defEqCtx_x3f_3008_ = lean_ctor_get(v_a_2899_, 4);
v_synthPendingDepth_3009_ = lean_ctor_get(v_a_2899_, 5);
v_canUnfold_x3f_3010_ = lean_ctor_get(v_a_2899_, 6);
v_univApprox_3011_ = lean_ctor_get_uint8(v_a_2899_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3012_ = lean_ctor_get_uint8(v_a_2899_, sizeof(void*)*7 + 2);
v_cacheInferType_3013_ = lean_ctor_get_uint8(v_a_2899_, sizeof(void*)*7 + 3);
v___x_3014_ = 2;
if (v_isShared_3003_ == 0)
{
v_config_3016_ = v___x_3002_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 0, v_foApprox_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 1, v_ctxApprox_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 2, v_quasiPatternApprox_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 3, v_constApprox_2986_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 4, v_isDefEqStuckEx_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 5, v_unificationHints_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 6, v_proofIrrelevance_2989_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 7, v_assignSyntheticOpaque_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 8, v_offsetCnstrs_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 10, v_etaStruct_2992_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 11, v_univApprox_2993_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 12, v_iota_2994_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 13, v_beta_2995_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 14, v_proj_2996_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 15, v_zeta_2997_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 16, v_zetaDelta_2998_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 17, v_zetaUnused_2999_);
lean_ctor_set_uint8(v_reuseFailAlloc_3072_, 18, v_zetaHave_3000_);
v_config_3016_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
uint64_t v___x_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; uint64_t v___x_3020_; uint64_t v___x_3021_; uint64_t v_key_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
lean_ctor_set_uint8(v_config_3016_, 9, v___x_3014_);
v___x_3017_ = l_Lean_Meta_Context_configKey(v_a_2899_);
v___x_3018_ = 3ULL;
v___x_3019_ = lean_uint64_shift_right(v___x_3017_, v___x_3018_);
v___x_3020_ = lean_uint64_shift_left(v___x_3019_, v___x_3018_);
v___x_3021_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4);
v_key_3022_ = lean_uint64_lor(v___x_3020_, v___x_3021_);
v___x_3023_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3023_, 0, v_config_3016_);
lean_ctor_set_uint64(v___x_3023_, sizeof(void*)*1, v_key_3022_);
lean_inc(v_canUnfold_x3f_3010_);
lean_inc(v_synthPendingDepth_3009_);
lean_inc(v_defEqCtx_x3f_3008_);
lean_inc_ref(v_localInstances_3007_);
lean_inc_ref(v_lctx_3006_);
lean_inc(v_zetaDeltaSet_3005_);
v___x_3024_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v_zetaDeltaSet_3005_);
lean_ctor_set(v___x_3024_, 2, v_lctx_3006_);
lean_ctor_set(v___x_3024_, 3, v_localInstances_3007_);
lean_ctor_set(v___x_3024_, 4, v_defEqCtx_x3f_3008_);
lean_ctor_set(v___x_3024_, 5, v_synthPendingDepth_3009_);
lean_ctor_set(v___x_3024_, 6, v_canUnfold_x3f_3010_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*7, v_trackZetaDelta_3004_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*7 + 1, v_univApprox_3011_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3012_);
lean_ctor_set_uint8(v___x_3024_, sizeof(void*)*7 + 3, v_cacheInferType_3013_);
v___x_3025_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_2904_, v___x_3024_, v_a_2900_, v_a_2901_, v_a_2902_);
lean_dec_ref_known(v___x_3024_, 7);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref_known(v___x_3025_, 1);
if (lean_obj_tag(v_a_3026_) == 1)
{
lean_object* v_val_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref_known(v_val_2910_, 1);
lean_del_object(v___x_2912_);
lean_dec_ref(v___x_2904_);
v_val_3027_ = lean_ctor_get(v_a_3026_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_a_3026_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3029_ = v_a_3026_;
v_isShared_3030_ = v_isSharedCheck_3063_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_val_3027_);
lean_dec(v_a_3026_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3063_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_Meta_Sym_shareCommonInc(v_val_3027_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v___x_3033_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2890_, v_info_2891_, v_a_3032_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3046_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3046_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3046_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3039_, 0, v_a_3034_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 0, v___x_3039_);
v___x_3041_ = v___x_3029_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v___x_3041_);
v___x_3043_ = v___x_3036_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_del_object(v___x_3029_);
v_a_3047_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3033_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3033_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_3029_);
lean_dec_ref(v_info_2891_);
lean_dec(v_goal_2890_);
v_a_3055_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3031_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3031_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
else
{
lean_dec(v_a_3026_);
v___y_2915_ = v_a_2892_;
v___y_2916_ = v_a_2893_;
v___y_2917_ = v_a_2894_;
v___y_2918_ = v_a_2895_;
v___y_2919_ = v_a_2896_;
v___y_2920_ = v_a_2897_;
v___y_2921_ = v_a_2898_;
v___y_2922_ = v_a_2899_;
v___y_2923_ = v_a_2900_;
v___y_2924_ = v_a_2901_;
v___y_2925_ = v_a_2902_;
goto v___jp_2914_;
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec_ref_known(v_val_2910_, 1);
lean_del_object(v___x_2912_);
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_info_2891_);
lean_dec(v_goal_2890_);
v_a_3064_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3025_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3025_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
}
}
else
{
v___y_2915_ = v_a_2892_;
v___y_2916_ = v_a_2893_;
v___y_2917_ = v_a_2894_;
v___y_2918_ = v_a_2895_;
v___y_2919_ = v_a_2896_;
v___y_2920_ = v_a_2897_;
v___y_2921_ = v_a_2898_;
v___y_2922_ = v_a_2899_;
v___y_2923_ = v_a_2900_;
v___y_2924_ = v_a_2901_;
v___y_2925_ = v_a_2902_;
goto v___jp_2914_;
}
v___jp_2914_:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_2910_, v_info_2891_, v___y_2916_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1);
v___x_2929_ = l_Lean_indentExpr(v___x_2904_);
lean_inc_ref(v___x_2929_);
v___x_2930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2930_, 0, v___x_2928_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2930_);
v___x_2932_ = v___x_2912_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
lean_object* v___x_2933_; 
v___x_2933_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2927_, v_goal_2890_, v___x_2932_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
if (lean_obj_tag(v_a_2934_) == 1)
{
lean_object* v_mvarIds_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v___x_2929_);
v_mvarIds_2935_ = lean_ctor_get(v_a_2934_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v_a_2934_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2937_ = v_a_2934_;
v_isShared_2938_ = v_isSharedCheck_2961_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_mvarIds_2935_);
lean_dec(v_a_2934_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2961_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2));
v___x_2940_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_2935_, v___x_2939_, v___y_2915_, v___y_2916_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
lean_dec(v_mvarIds_2935_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2952_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2952_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2952_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2947_; 
v___x_2945_ = lean_array_to_list(v_a_2941_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 0, v___x_2945_);
v___x_2947_ = v___x_2937_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2945_);
v___x_2947_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
lean_object* v___x_2949_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2947_);
v___x_2949_ = v___x_2943_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
lean_del_object(v___x_2937_);
v_a_2953_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2940_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2940_);
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
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_dec(v_a_2934_);
v___x_2962_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
lean_ctor_set(v___x_2963_, 1, v___x_2929_);
v___x_2964_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2963_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
return v___x_2964_;
}
}
else
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2972_; 
lean_dec_ref(v___x_2929_);
v_a_2965_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2972_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2972_ == 0)
{
v___x_2967_ = v___x_2933_;
v_isShared_2968_ = v_isSharedCheck_2972_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2933_);
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
}
else
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_del_object(v___x_2912_);
lean_dec_ref(v___x_2904_);
lean_dec(v_goal_2890_);
v_a_2974_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2926_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2926_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
}
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3077_; 
lean_dec(v_a_2906_);
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_info_2891_);
lean_dec(v_goal_2890_);
v___x_3075_ = lean_box(0);
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 0, v___x_3075_);
v___x_3077_ = v___x_2908_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v___x_2904_);
lean_dec_ref(v_info_2891_);
lean_dec(v_goal_2890_);
v_a_3080_ = lean_ctor_get(v___x_2905_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_2905_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_2905_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_2905_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_3088_, lean_object* v_info_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_, lean_object* v_a_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_3088_, v_info_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_, v_a_3100_);
lean_dec(v_a_3100_);
lean_dec_ref(v_a_3099_);
lean_dec(v_a_3098_);
lean_dec_ref(v_a_3097_);
lean_dec(v_a_3096_);
lean_dec_ref(v_a_3095_);
lean_dec(v_a_3094_);
lean_dec_ref(v_a_3093_);
lean_dec(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3103_, lean_object* v_as_x27_3104_, lean_object* v_b_3105_, lean_object* v_a_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3104_, v_b_3105_, v___y_3107_, v___y_3108_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3120_, lean_object* v_as_x27_3121_, lean_object* v_b_3122_, lean_object* v_a_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(v_as_3120_, v_as_x27_3121_, v_b_3122_, v_a_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v_as_x27_3121_);
lean_dec(v_as_3120_);
return v_res_3136_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3139_ = l_Lean_stringToMessageData(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3140_, lean_object* v_info_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_){
_start:
{
lean_object* v___x_3154_; lean_object* v_f_3155_; lean_object* v___x_3156_; 
v___x_3154_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3141_);
v_f_3155_ = l_Lean_Expr_getAppFn(v___x_3154_);
v___x_3156_ = l_Lean_Expr_fvarId_x3f(v_f_3155_);
lean_dec_ref(v_f_3155_);
if (lean_obj_tag(v___x_3156_) == 1)
{
lean_object* v_val_3157_; uint8_t v___x_3158_; lean_object* v___x_3159_; 
v_val_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc_n(v_val_3157_, 2);
lean_dec_ref_known(v___x_3156_, 1);
v___x_3158_ = 0;
v___x_3159_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3157_, v___x_3158_, v_a_3149_, v_a_3151_, v_a_3152_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3247_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3162_ = v___x_3159_;
v_isShared_3163_ = v_isSharedCheck_3247_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3247_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
if (lean_obj_tag(v_a_3160_) == 1)
{
lean_object* v_val_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3242_; 
lean_del_object(v___x_3162_);
v_val_3164_ = lean_ctor_get(v_a_3160_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_a_3160_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3166_ = v_a_3160_;
v_isShared_3167_ = v_isSharedCheck_3242_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_val_3164_);
lean_dec(v_a_3160_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3242_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3174_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v_options_3214_; uint8_t v_hasTrace_3215_; 
v_options_3214_ = lean_ctor_get(v_a_3151_, 2);
v_hasTrace_3215_ = lean_ctor_get_uint8(v_options_3214_, sizeof(void*)*1);
if (v_hasTrace_3215_ == 0)
{
lean_dec(v_val_3157_);
v___y_3169_ = v_a_3142_;
v___y_3170_ = v_a_3143_;
v___y_3171_ = v_a_3144_;
v___y_3172_ = v_a_3145_;
v___y_3173_ = v_a_3146_;
v___y_3174_ = v_a_3147_;
v___y_3175_ = v_a_3148_;
v___y_3176_ = v_a_3149_;
v___y_3177_ = v_a_3150_;
v___y_3178_ = v_a_3151_;
v___y_3179_ = v_a_3152_;
goto v___jp_3168_;
}
else
{
lean_object* v_inheritedTraceOptions_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v_inheritedTraceOptions_3216_ = lean_ctor_get(v_a_3151_, 13);
v___x_3217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3218_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3219_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3216_, v_options_3214_, v___x_3218_);
if (v___x_3219_ == 0)
{
lean_dec(v_val_3157_);
v___y_3169_ = v_a_3142_;
v___y_3170_ = v_a_3143_;
v___y_3171_ = v_a_3144_;
v___y_3172_ = v_a_3145_;
v___y_3173_ = v_a_3146_;
v___y_3174_ = v_a_3147_;
v___y_3175_ = v_a_3148_;
v___y_3176_ = v_a_3149_;
v___y_3177_ = v_a_3150_;
v___y_3178_ = v_a_3151_;
v___y_3179_ = v_a_3152_;
goto v___jp_3168_;
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_FVarId_getUserName___redArg(v_val_3157_, v_a_3149_, v_a_3151_, v_a_3152_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3223_ = l_Lean_MessageData_ofName(v_a_3221_);
v___x_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
v___x_3225_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3217_, v___x_3224_, v_a_3149_, v_a_3150_, v_a_3151_, v_a_3152_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_dec_ref_known(v___x_3225_, 1);
v___y_3169_ = v_a_3142_;
v___y_3170_ = v_a_3143_;
v___y_3171_ = v_a_3144_;
v___y_3172_ = v_a_3145_;
v___y_3173_ = v_a_3146_;
v___y_3174_ = v_a_3147_;
v___y_3175_ = v_a_3148_;
v___y_3176_ = v_a_3149_;
v___y_3177_ = v_a_3150_;
v___y_3178_ = v_a_3151_;
v___y_3179_ = v_a_3152_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3166_);
lean_dec(v_val_3164_);
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_info_3141_);
lean_dec(v_goal_3140_);
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_del_object(v___x_3166_);
lean_dec(v_val_3164_);
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_info_3141_);
lean_dec(v_goal_3140_);
v_a_3234_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3220_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3220_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
v___jp_3168_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3180_ = l_Lean_Expr_getAppNumArgs(v___x_3154_);
v___x_3181_ = lean_mk_empty_array_with_capacity(v___x_3180_);
lean_dec(v___x_3180_);
v___x_3182_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3154_, v___x_3181_);
v___x_3183_ = l_Lean_Expr_betaRev(v_val_3164_, v___x_3182_, v___x_3158_, v___x_3158_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = l_Lean_Meta_Sym_shareCommonInc(v___x_3183_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3140_, v_info_3141_, v_a_3185_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3197_; 
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3197_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3197_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3167_ == 0)
{
lean_ctor_set(v___x_3166_, 0, v_a_3187_);
v___x_3192_ = v___x_3166_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
lean_object* v___x_3194_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3192_);
v___x_3194_ = v___x_3189_;
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
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_del_object(v___x_3166_);
v_a_3198_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3186_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3186_);
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
lean_del_object(v___x_3166_);
lean_dec_ref(v_info_3141_);
lean_dec(v_goal_3140_);
v_a_3206_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3184_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3184_);
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
}
}
else
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
lean_dec(v_a_3160_);
lean_dec(v_val_3157_);
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_info_3141_);
lean_dec(v_goal_3140_);
v___x_3243_ = lean_box(0);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3243_);
v___x_3245_ = v___x_3162_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
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
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec(v_val_3157_);
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_info_3141_);
lean_dec(v_goal_3140_);
v_a_3248_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3159_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3159_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
else
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec(v___x_3156_);
lean_dec_ref(v___x_3154_);
lean_dec_ref(v_info_3141_);
lean_dec(v_goal_3140_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
return v___x_3257_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3258_, lean_object* v_info_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_3258_, v_info_3259_, v_a_3260_, v_a_3261_, v_a_3262_, v_a_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec_ref(v_a_3267_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
lean_dec(v_a_3264_);
lean_dec_ref(v_a_3263_);
lean_dec(v_a_3262_);
lean_dec(v_a_3261_);
lean_dec_ref(v_a_3260_);
return v_res_3272_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0(void){
_start:
{
uint8_t v___x_3273_; uint64_t v___x_3274_; 
v___x_3273_ = 3;
v___x_3274_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3273_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3275_, lean_object* v_info_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_){
_start:
{
lean_object* v___x_3289_; lean_object* v_a_3291_; lean_object* v_f_3352_; 
v___x_3289_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3276_);
v_f_3352_ = l_Lean_Expr_getAppFn(v___x_3289_);
if (lean_obj_tag(v_f_3352_) == 11)
{
lean_object* v___x_3353_; uint8_t v_foApprox_3354_; uint8_t v_ctxApprox_3355_; uint8_t v_quasiPatternApprox_3356_; uint8_t v_constApprox_3357_; uint8_t v_isDefEqStuckEx_3358_; uint8_t v_unificationHints_3359_; uint8_t v_proofIrrelevance_3360_; uint8_t v_assignSyntheticOpaque_3361_; uint8_t v_offsetCnstrs_3362_; uint8_t v_etaStruct_3363_; uint8_t v_univApprox_3364_; uint8_t v_iota_3365_; uint8_t v_beta_3366_; uint8_t v_proj_3367_; uint8_t v_zeta_3368_; uint8_t v_zetaDelta_3369_; uint8_t v_zetaUnused_3370_; uint8_t v_zetaHave_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3408_; 
v___x_3353_ = l_Lean_Meta_Context_config(v_a_3284_);
v_foApprox_3354_ = lean_ctor_get_uint8(v___x_3353_, 0);
v_ctxApprox_3355_ = lean_ctor_get_uint8(v___x_3353_, 1);
v_quasiPatternApprox_3356_ = lean_ctor_get_uint8(v___x_3353_, 2);
v_constApprox_3357_ = lean_ctor_get_uint8(v___x_3353_, 3);
v_isDefEqStuckEx_3358_ = lean_ctor_get_uint8(v___x_3353_, 4);
v_unificationHints_3359_ = lean_ctor_get_uint8(v___x_3353_, 5);
v_proofIrrelevance_3360_ = lean_ctor_get_uint8(v___x_3353_, 6);
v_assignSyntheticOpaque_3361_ = lean_ctor_get_uint8(v___x_3353_, 7);
v_offsetCnstrs_3362_ = lean_ctor_get_uint8(v___x_3353_, 8);
v_etaStruct_3363_ = lean_ctor_get_uint8(v___x_3353_, 10);
v_univApprox_3364_ = lean_ctor_get_uint8(v___x_3353_, 11);
v_iota_3365_ = lean_ctor_get_uint8(v___x_3353_, 12);
v_beta_3366_ = lean_ctor_get_uint8(v___x_3353_, 13);
v_proj_3367_ = lean_ctor_get_uint8(v___x_3353_, 14);
v_zeta_3368_ = lean_ctor_get_uint8(v___x_3353_, 15);
v_zetaDelta_3369_ = lean_ctor_get_uint8(v___x_3353_, 16);
v_zetaUnused_3370_ = lean_ctor_get_uint8(v___x_3353_, 17);
v_zetaHave_3371_ = lean_ctor_get_uint8(v___x_3353_, 18);
v_isSharedCheck_3408_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3408_ == 0)
{
v___x_3373_ = v___x_3353_;
v_isShared_3374_ = v_isSharedCheck_3408_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v___x_3353_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3408_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
uint8_t v_trackZetaDelta_3375_; lean_object* v_zetaDeltaSet_3376_; lean_object* v_lctx_3377_; lean_object* v_localInstances_3378_; lean_object* v_defEqCtx_x3f_3379_; lean_object* v_synthPendingDepth_3380_; lean_object* v_canUnfold_x3f_3381_; uint8_t v_univApprox_3382_; uint8_t v_inTypeClassResolution_3383_; uint8_t v_cacheInferType_3384_; uint8_t v___x_3385_; lean_object* v_config_3387_; 
v_trackZetaDelta_3375_ = lean_ctor_get_uint8(v_a_3284_, sizeof(void*)*7);
v_zetaDeltaSet_3376_ = lean_ctor_get(v_a_3284_, 1);
v_lctx_3377_ = lean_ctor_get(v_a_3284_, 2);
v_localInstances_3378_ = lean_ctor_get(v_a_3284_, 3);
v_defEqCtx_x3f_3379_ = lean_ctor_get(v_a_3284_, 4);
v_synthPendingDepth_3380_ = lean_ctor_get(v_a_3284_, 5);
v_canUnfold_x3f_3381_ = lean_ctor_get(v_a_3284_, 6);
v_univApprox_3382_ = lean_ctor_get_uint8(v_a_3284_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3383_ = lean_ctor_get_uint8(v_a_3284_, sizeof(void*)*7 + 2);
v_cacheInferType_3384_ = lean_ctor_get_uint8(v_a_3284_, sizeof(void*)*7 + 3);
v___x_3385_ = 3;
if (v_isShared_3374_ == 0)
{
v_config_3387_ = v___x_3373_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 0, v_foApprox_3354_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 1, v_ctxApprox_3355_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 2, v_quasiPatternApprox_3356_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 3, v_constApprox_3357_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 4, v_isDefEqStuckEx_3358_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 5, v_unificationHints_3359_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 6, v_proofIrrelevance_3360_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 7, v_assignSyntheticOpaque_3361_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 8, v_offsetCnstrs_3362_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 10, v_etaStruct_3363_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 11, v_univApprox_3364_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 12, v_iota_3365_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 13, v_beta_3366_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 14, v_proj_3367_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 15, v_zeta_3368_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 16, v_zetaDelta_3369_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 17, v_zetaUnused_3370_);
lean_ctor_set_uint8(v_reuseFailAlloc_3407_, 18, v_zetaHave_3371_);
v_config_3387_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
uint64_t v___x_3388_; uint64_t v___x_3389_; uint64_t v___x_3390_; uint64_t v___x_3391_; uint64_t v___x_3392_; uint64_t v_key_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
lean_ctor_set_uint8(v_config_3387_, 9, v___x_3385_);
v___x_3388_ = l_Lean_Meta_Context_configKey(v_a_3284_);
v___x_3389_ = 3ULL;
v___x_3390_ = lean_uint64_shift_right(v___x_3388_, v___x_3389_);
v___x_3391_ = lean_uint64_shift_left(v___x_3390_, v___x_3389_);
v___x_3392_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0);
v_key_3393_ = lean_uint64_lor(v___x_3391_, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3394_, 0, v_config_3387_);
lean_ctor_set_uint64(v___x_3394_, sizeof(void*)*1, v_key_3393_);
lean_inc(v_canUnfold_x3f_3381_);
lean_inc(v_synthPendingDepth_3380_);
lean_inc(v_defEqCtx_x3f_3379_);
lean_inc_ref(v_localInstances_3378_);
lean_inc_ref(v_lctx_3377_);
lean_inc(v_zetaDeltaSet_3376_);
v___x_3395_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v_zetaDeltaSet_3376_);
lean_ctor_set(v___x_3395_, 2, v_lctx_3377_);
lean_ctor_set(v___x_3395_, 3, v_localInstances_3378_);
lean_ctor_set(v___x_3395_, 4, v_defEqCtx_x3f_3379_);
lean_ctor_set(v___x_3395_, 5, v_synthPendingDepth_3380_);
lean_ctor_set(v___x_3395_, 6, v_canUnfold_x3f_3381_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7, v_trackZetaDelta_3375_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7 + 1, v_univApprox_3382_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3383_);
lean_ctor_set_uint8(v___x_3395_, sizeof(void*)*7 + 3, v_cacheInferType_3384_);
v___x_3396_ = l_Lean_Meta_reduceProj_x3f(v_f_3352_, v___x_3395_, v_a_3285_, v_a_3286_, v_a_3287_);
lean_dec_ref_known(v___x_3395_, 7);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
v_a_3291_ = v_a_3397_;
goto v___jp_3290_;
}
else
{
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3398_; 
v_a_3398_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3398_);
lean_dec_ref_known(v___x_3396_, 1);
v_a_3291_ = v_a_3398_;
goto v___jp_3290_;
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_dec_ref(v___x_3289_);
lean_dec_ref(v_info_3276_);
lean_dec(v_goal_3275_);
v_a_3399_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3396_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3396_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_dec_ref(v_f_3352_);
lean_dec_ref(v___x_3289_);
lean_dec_ref(v_info_3276_);
lean_dec(v_goal_3275_);
v___x_3409_ = lean_box(0);
v___x_3410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3409_);
return v___x_3410_;
}
v___jp_3290_:
{
if (lean_obj_tag(v_a_3291_) == 1)
{
lean_object* v_val_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3349_; 
v_val_3292_ = lean_ctor_get(v_a_3291_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v_a_3291_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3294_ = v_a_3291_;
v_isShared_3295_ = v_isSharedCheck_3349_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_val_3292_);
lean_dec(v_a_3291_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3349_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; 
v___x_3296_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3292_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
v___x_3298_ = l_Lean_Meta_Sym_shareCommon(v_a_3297_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v___x_3300_ = l_Lean_Expr_getAppNumArgs(v___x_3289_);
v___x_3301_ = lean_mk_empty_array_with_capacity(v___x_3300_);
lean_dec(v___x_3300_);
v___x_3302_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3289_, v___x_3301_);
v___x_3303_ = l_Lean_Meta_Sym_betaRevS(v_a_3299_, v___x_3302_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3303_) == 0)
{
lean_object* v_a_3304_; lean_object* v___x_3305_; 
v_a_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_a_3304_);
lean_dec_ref_known(v___x_3303_, 1);
v___x_3305_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3275_, v_info_3276_, v_a_3304_, v_a_3277_, v_a_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3316_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3308_ = v___x_3305_;
v_isShared_3309_ = v_isSharedCheck_3316_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_a_3306_);
lean_dec(v___x_3305_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3316_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v___x_3311_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 0, v_a_3306_);
v___x_3311_ = v___x_3294_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3306_);
v___x_3311_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3313_; 
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 0, v___x_3311_);
v___x_3313_ = v___x_3308_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3311_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_del_object(v___x_3294_);
v_a_3317_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3305_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3305_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_del_object(v___x_3294_);
lean_dec_ref(v_info_3276_);
lean_dec(v_goal_3275_);
v_a_3325_ = lean_ctor_get(v___x_3303_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3303_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3303_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3303_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_del_object(v___x_3294_);
lean_dec_ref(v___x_3289_);
lean_dec_ref(v_info_3276_);
lean_dec(v_goal_3275_);
v_a_3333_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3298_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3298_);
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
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_del_object(v___x_3294_);
lean_dec_ref(v___x_3289_);
lean_dec_ref(v_info_3276_);
lean_dec(v_goal_3275_);
v_a_3341_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3296_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3296_);
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
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec(v_a_3291_);
lean_dec_ref(v___x_3289_);
lean_dec_ref(v_info_3276_);
lean_dec(v_goal_3275_);
v___x_3350_ = lean_box(0);
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_3411_, lean_object* v_info_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_3411_, v_info_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
lean_dec(v_a_3423_);
lean_dec_ref(v_a_3422_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
lean_dec(v_a_3417_);
lean_dec_ref(v_a_3416_);
lean_dec(v_a_3415_);
lean_dec(v_a_3414_);
lean_dec_ref(v_a_3413_);
return v_res_3425_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_3428_ = l_Lean_stringToMessageData(v___x_3427_);
return v___x_3428_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_3431_ = l_Lean_stringToMessageData(v___x_3430_);
return v___x_3431_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_3434_ = l_Lean_stringToMessageData(v___x_3433_);
return v___x_3434_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_3437_ = l_Lean_stringToMessageData(v___x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
if (lean_obj_tag(v_a_3438_) == 0)
{
lean_object* v___x_3440_; 
v___x_3440_ = l_List_reverse___redArg(v_a_3439_);
return v___x_3440_;
}
else
{
lean_object* v_head_3441_; lean_object* v_tail_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3470_; 
v_head_3441_ = lean_ctor_get(v_a_3438_, 0);
v_tail_3442_ = lean_ctor_get(v_a_3438_, 1);
v_isSharedCheck_3470_ = !lean_is_exclusive(v_a_3438_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3444_ = v_a_3438_;
v_isShared_3445_ = v_isSharedCheck_3470_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_tail_3442_);
lean_inc(v_head_3441_);
lean_dec(v_a_3438_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3470_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
lean_object* v___y_3447_; 
switch(lean_obj_tag(v_head_3441_))
{
case 0:
{
lean_object* v_declName_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_declName_3452_ = lean_ctor_get(v_head_3441_, 0);
lean_inc(v_declName_3452_);
lean_dec_ref_known(v_head_3441_, 1);
v___x_3453_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3454_ = l_Lean_MessageData_ofName(v_declName_3452_);
v___x_3455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3455_, 0, v___x_3453_);
lean_ctor_set(v___x_3455_, 1, v___x_3454_);
v___y_3447_ = v___x_3455_;
goto v___jp_3446_;
}
case 1:
{
lean_object* v_fvarId_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_fvarId_3456_ = lean_ctor_get(v_head_3441_, 0);
lean_inc(v_fvarId_3456_);
lean_dec_ref_known(v_head_3441_, 1);
v___x_3457_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3458_ = l_Lean_mkFVar(v_fvarId_3456_);
v___x_3459_ = l_Lean_MessageData_ofExpr(v___x_3458_);
v___x_3460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3457_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___y_3447_ = v___x_3460_;
goto v___jp_3446_;
}
default: 
{
lean_object* v_ref_3461_; lean_object* v_proof_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v_ref_3461_ = lean_ctor_get(v_head_3441_, 1);
lean_inc(v_ref_3461_);
v_proof_3462_ = lean_ctor_get(v_head_3441_, 2);
lean_inc_ref(v_proof_3462_);
lean_dec_ref_known(v_head_3441_, 3);
v___x_3463_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3464_ = l_Lean_MessageData_ofSyntax(v_ref_3461_);
v___x_3465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
v___x_3466_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3465_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = l_Lean_MessageData_ofExpr(v_proof_3462_);
v___x_3469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3469_, 0, v___x_3467_);
lean_ctor_set(v___x_3469_, 1, v___x_3468_);
v___y_3447_ = v___x_3469_;
goto v___jp_3446_;
}
}
v___jp_3446_:
{
lean_object* v___x_3449_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 1, v_a_3439_);
lean_ctor_set(v___x_3444_, 0, v___y_3447_);
v___x_3449_ = v___x_3444_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___y_3447_);
lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_a_3439_);
v___x_3449_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
v_a_3438_ = v_tail_3442_;
v_a_3439_ = v___x_3449_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_3471_, size_t v_i_3472_, lean_object* v_bs_3473_){
_start:
{
uint8_t v___x_3474_; 
v___x_3474_ = lean_usize_dec_lt(v_i_3472_, v_sz_3471_);
if (v___x_3474_ == 0)
{
return v_bs_3473_;
}
else
{
lean_object* v_v_3475_; lean_object* v_proof_3476_; lean_object* v___x_3477_; lean_object* v_bs_x27_3478_; size_t v___x_3479_; size_t v___x_3480_; lean_object* v___x_3481_; 
v_v_3475_ = lean_array_uget_borrowed(v_bs_3473_, v_i_3472_);
v_proof_3476_ = lean_ctor_get(v_v_3475_, 1);
lean_inc_ref(v_proof_3476_);
v___x_3477_ = lean_unsigned_to_nat(0u);
v_bs_x27_3478_ = lean_array_uset(v_bs_3473_, v_i_3472_, v___x_3477_);
v___x_3479_ = ((size_t)1ULL);
v___x_3480_ = lean_usize_add(v_i_3472_, v___x_3479_);
v___x_3481_ = lean_array_uset(v_bs_x27_3478_, v_i_3472_, v_proof_3476_);
v_i_3472_ = v___x_3480_;
v_bs_3473_ = v___x_3481_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_3483_, lean_object* v_i_3484_, lean_object* v_bs_3485_){
_start:
{
size_t v_sz_boxed_3486_; size_t v_i_boxed_3487_; lean_object* v_res_3488_; 
v_sz_boxed_3486_ = lean_unbox_usize(v_sz_3483_);
lean_dec(v_sz_3483_);
v_i_boxed_3487_ = lean_unbox_usize(v_i_3484_);
lean_dec(v_i_3484_);
v_res_3488_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_3486_, v_i_boxed_3487_, v_bs_3485_);
return v_res_3488_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; 
v___x_3490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_3491_ = l_Lean_stringToMessageData(v___x_3490_);
return v___x_3491_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3493_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_3494_ = l_Lean_stringToMessageData(v___x_3493_);
return v___x_3494_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_3497_ = l_Lean_stringToMessageData(v___x_3496_);
return v___x_3497_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3499_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_3500_ = l_Lean_stringToMessageData(v___x_3499_);
return v___x_3500_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_3504_, lean_object* v_monad_3505_, lean_object* v_thms_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
uint8_t v_errorOnMissingSpec_3513_; 
v_errorOnMissingSpec_3513_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*4 + 2);
if (v_errorOnMissingSpec_3513_ == 0)
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_3514_, 0, v_prog_3504_);
lean_ctor_set(v___x_3514_, 1, v_monad_3505_);
lean_ctor_set(v___x_3514_, 2, v_thms_3506_);
v___x_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3515_, 0, v___x_3514_);
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
return v___x_3516_;
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; 
v___x_3517_ = lean_array_get_size(v_thms_3506_);
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3519_ = lean_nat_dec_eq(v___x_3517_, v___x_3518_);
if (v___x_3519_ == 0)
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; size_t v_sz_3529_; size_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3520_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_3521_ = l_Lean_MessageData_ofExpr(v_monad_3505_);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3522_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
v___x_3525_ = l_Lean_MessageData_ofExpr(v_prog_3504_);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v_sz_3529_ = lean_array_size(v_thms_3506_);
v___x_3530_ = ((size_t)0ULL);
v___x_3531_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_3529_, v___x_3530_, v_thms_3506_);
v___x_3532_ = lean_array_to_list(v___x_3531_);
v___x_3533_ = lean_box(0);
v___x_3534_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_3532_, v___x_3533_);
v___x_3535_ = l_Lean_MessageData_ofList(v___x_3534_);
v___x_3536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3528_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3536_);
lean_ctor_set(v___x_3538_, 1, v___x_3537_);
v___x_3539_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3538_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
return v___x_3539_;
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec_ref(v_thms_3506_);
lean_dec_ref(v_monad_3505_);
v___x_3540_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_3541_ = l_Lean_MessageData_ofExpr(v_prog_3504_);
v___x_3542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3540_);
lean_ctor_set(v___x_3542_, 1, v___x_3541_);
v___x_3543_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3542_);
lean_ctor_set(v___x_3544_, 1, v___x_3543_);
v___x_3545_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3544_, v_a_3508_, v_a_3509_, v_a_3510_, v_a_3511_);
return v___x_3545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_3546_, lean_object* v_monad_3547_, lean_object* v_thms_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3546_, v_monad_3547_, v_thms_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_3556_, lean_object* v_monad_3557_, lean_object* v_thms_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v___x_3571_; 
v___x_3571_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3556_, v_monad_3557_, v_thms_3558_, v_a_3559_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
return v___x_3571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_3572_, lean_object* v_monad_3573_, lean_object* v_thms_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(v_prog_3572_, v_monad_3573_, v_thms_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
lean_dec(v_a_3585_);
lean_dec_ref(v_a_3584_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec(v_a_3576_);
lean_dec_ref(v_a_3575_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_3588_, lean_object* v_a_3589_){
_start:
{
if (lean_obj_tag(v_a_3588_) == 0)
{
lean_object* v___x_3590_; 
v___x_3590_ = l_List_reverse___redArg(v_a_3589_);
return v___x_3590_;
}
else
{
lean_object* v_head_3591_; lean_object* v_tail_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3601_; 
v_head_3591_ = lean_ctor_get(v_a_3588_, 0);
v_tail_3592_ = lean_ctor_get(v_a_3588_, 1);
v_isSharedCheck_3601_ = !lean_is_exclusive(v_a_3588_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3594_ = v_a_3588_;
v_isShared_3595_ = v_isSharedCheck_3601_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_tail_3592_);
lean_inc(v_head_3591_);
lean_dec(v_a_3588_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3601_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v___x_3598_; 
v___x_3596_ = l_Lean_MessageData_ofExpr(v_head_3591_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 1, v_a_3589_);
lean_ctor_set(v___x_3594_, 0, v___x_3596_);
v___x_3598_ = v___x_3594_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3596_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_a_3589_);
v___x_3598_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
v_a_3588_ = v_tail_3592_;
v_a_3589_ = v___x_3598_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_3604_ = l_Lean_stringToMessageData(v___x_3603_);
return v___x_3604_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_3607_ = l_Lean_stringToMessageData(v___x_3606_);
return v___x_3607_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_3610_ = l_Lean_stringToMessageData(v___x_3609_);
return v___x_3610_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_3613_ = l_Lean_stringToMessageData(v___x_3612_);
return v___x_3613_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_3616_ = l_Lean_stringToMessageData(v___x_3615_);
return v___x_3616_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; 
v___x_3618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_3619_ = l_Lean_stringToMessageData(v___x_3618_);
return v___x_3619_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_3622_ = l_Lean_stringToMessageData(v___x_3621_);
return v___x_3622_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_3625_ = l_Lean_stringToMessageData(v___x_3624_);
return v___x_3625_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_3628_ = l_Lean_stringToMessageData(v___x_3627_);
return v___x_3628_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_3631_ = l_Lean_stringToMessageData(v___x_3630_);
return v___x_3631_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3633_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_3634_ = l_Lean_stringToMessageData(v___x_3633_);
return v___x_3634_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23(void){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22));
v___x_3637_ = l_Lean_stringToMessageData(v___x_3636_);
return v___x_3637_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24));
v___x_3640_ = l_Lean_stringToMessageData(v___x_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_scope_3641_, lean_object* v_goal_3642_, lean_object* v_info_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___y_3657_; lean_object* v___y_3658_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3701_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; uint8_t v___y_3856_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v_options_3906_; lean_object* v_inheritedTraceOptions_3907_; uint8_t v_hasTrace_3908_; lean_object* v_cls_3909_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; 
v_options_3906_ = lean_ctor_get(v_a_3653_, 2);
v_inheritedTraceOptions_3907_ = lean_ctor_get(v_a_3653_, 13);
v_hasTrace_3908_ = lean_ctor_get_uint8(v_options_3906_, sizeof(void*)*1);
v_cls_3909_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_3908_ == 0)
{
v___y_3938_ = v_a_3644_;
v___y_3939_ = v_a_3645_;
v___y_3940_ = v_a_3646_;
v___y_3941_ = v_a_3647_;
v___y_3942_ = v_a_3648_;
v___y_3943_ = v_a_3649_;
v___y_3944_ = v_a_3650_;
v___y_3945_ = v_a_3651_;
v___y_3946_ = v_a_3652_;
v___y_3947_ = v_a_3653_;
v___y_3948_ = v_a_3654_;
goto v___jp_3937_;
}
else
{
lean_object* v___x_4013_; uint8_t v___x_4014_; 
v___x_4013_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3907_, v_options_3906_, v___x_4013_);
if (v___x_4014_ == 0)
{
v___y_3938_ = v_a_3644_;
v___y_3939_ = v_a_3645_;
v___y_3940_ = v_a_3646_;
v___y_3941_ = v_a_3647_;
v___y_3942_ = v_a_3648_;
v___y_3943_ = v_a_3649_;
v___y_3944_ = v_a_3650_;
v___y_3945_ = v_a_3651_;
v___y_3946_ = v_a_3652_;
v___y_3947_ = v_a_3653_;
v___y_3948_ = v_a_3654_;
goto v___jp_3937_;
}
else
{
lean_object* v_excessArgs_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_excessArgs_4015_ = lean_ctor_get(v_info_3643_, 2);
v___x_4016_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23);
v___x_4017_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3643_);
v___x_4018_ = l_Lean_MessageData_ofExpr(v___x_4017_);
v___x_4019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4019_, 0, v___x_4016_);
lean_ctor_set(v___x_4019_, 1, v___x_4018_);
v___x_4020_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25);
v___x_4021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4021_, 0, v___x_4019_);
lean_ctor_set(v___x_4021_, 1, v___x_4020_);
lean_inc_ref(v_excessArgs_4015_);
v___x_4022_ = lean_array_to_list(v_excessArgs_4015_);
v___x_4023_ = lean_box(0);
v___x_4024_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_4022_, v___x_4023_);
v___x_4025_ = l_Lean_MessageData_ofList(v___x_4024_);
v___x_4026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4021_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3909_, v___x_4026_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_dec_ref_known(v___x_4027_, 1);
v___y_3938_ = v_a_3644_;
v___y_3939_ = v_a_3645_;
v___y_3940_ = v_a_3646_;
v___y_3941_ = v_a_3647_;
v___y_3942_ = v_a_3648_;
v___y_3943_ = v_a_3649_;
v___y_3944_ = v_a_3650_;
v___y_3945_ = v_a_3651_;
v___y_3946_ = v_a_3652_;
v___y_3947_ = v_a_3653_;
v___y_3948_ = v_a_3654_;
goto v___jp_3937_;
}
else
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4035_; 
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
lean_dec_ref(v_scope_3641_);
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4035_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4035_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4035_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
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
v___jp_3656_:
{
lean_object* v_excessArgs_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v_excessArgs_3666_ = lean_ctor_get(v_info_3643_, 2);
lean_inc_ref(v_excessArgs_3666_);
lean_inc_ref(v___y_3661_);
v___x_3667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___y_3661_);
lean_ctor_set(v___x_3667_, 1, v___y_3665_);
v___x_3668_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3667_);
lean_ctor_set(v___x_3669_, 1, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___y_3662_);
v___x_3671_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
v___x_3673_ = l_Lean_indentExpr(v___y_3658_);
v___x_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3672_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v___x_3675_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_3643_);
lean_dec_ref(v_info_3643_);
v___x_3678_ = l_Lean_indentExpr(v___x_3677_);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3676_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = lean_array_to_list(v_excessArgs_3666_);
v___x_3683_ = lean_box(0);
v___x_3684_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3682_, v___x_3683_);
v___x_3685_ = l_Lean_MessageData_ofList(v___x_3684_);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3681_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = l_Lean_indentExpr(v___y_3657_);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3688_);
lean_ctor_set(v___x_3690_, 1, v___x_3689_);
v___x_3691_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3690_, v___y_3664_, v___y_3660_, v___y_3663_, v___y_3659_);
return v___x_3691_;
}
v___jp_3692_:
{
if (lean_obj_tag(v___y_3707_) == 0)
{
lean_object* v_a_3708_; 
v_a_3708_ = lean_ctor_get(v___y_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___y_3707_, 1);
if (lean_obj_tag(v_a_3708_) == 1)
{
lean_object* v_val_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3779_; 
v_val_3709_ = lean_ctor_get(v_a_3708_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_a_3708_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3711_ = v_a_3708_;
v_isShared_3712_ = v_isSharedCheck_3779_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_val_3709_);
lean_dec(v_a_3708_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3779_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3713_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
v___x_3714_ = l_Lean_indentExpr(v___y_3703_);
lean_inc_ref(v___x_3714_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 0, v___x_3715_);
v___x_3717_ = v___x_3711_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
lean_object* v___x_3718_; 
lean_inc(v_goal_3642_);
lean_inc(v_val_3709_);
v___x_3718_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_3709_, v_goal_3642_, v___x_3717_, v___y_3704_, v___y_3701_, v___y_3695_, v___y_3702_, v___y_3693_, v___y_3699_, v___y_3698_, v___y_3697_, v___y_3700_, v___y_3696_, v___y_3694_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3769_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3721_ = v___x_3718_;
v_isShared_3722_ = v_isSharedCheck_3769_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_a_3719_);
lean_dec(v___x_3718_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3769_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
if (lean_obj_tag(v_a_3719_) == 1)
{
lean_object* v_mvarIds_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
lean_dec_ref(v___x_3714_);
lean_dec(v_val_3709_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
v_mvarIds_3723_ = lean_ctor_get(v_a_3719_, 0);
lean_inc(v_mvarIds_3723_);
lean_dec_ref_known(v_a_3719_, 1);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___y_3706_);
lean_ctor_set(v___x_3724_, 1, v_mvarIds_3723_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v___x_3724_);
v___x_3726_ = v___x_3721_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
else
{
lean_object* v_expr_3728_; lean_object* v___x_3729_; 
lean_del_object(v___x_3721_);
lean_dec(v_a_3719_);
lean_dec_ref(v___y_3706_);
v_expr_3728_ = lean_ctor_get(v_val_3709_, 0);
lean_inc_ref(v_expr_3728_);
lean_dec(v_val_3709_);
lean_inc(v___y_3694_);
lean_inc_ref(v___y_3696_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3697_);
v___x_3729_ = lean_infer_type(v_expr_3728_, v___y_3697_, v___y_3700_, v___y_3696_, v___y_3694_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v_a_3730_; lean_object* v___x_3731_; 
v_a_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_a_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = l_Lean_MVarId_getType(v_goal_3642_, v___y_3697_, v___y_3700_, v___y_3696_, v___y_3694_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_object* v_a_3732_; lean_object* v_proof_3733_; lean_object* v___x_3734_; 
v_a_3732_ = lean_ctor_get(v___x_3731_, 0);
lean_inc(v_a_3732_);
lean_dec_ref_known(v___x_3731_, 1);
v_proof_3733_ = lean_ctor_get(v___y_3705_, 1);
lean_inc_ref(v_proof_3733_);
lean_dec_ref(v___y_3705_);
v___x_3734_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
switch(lean_obj_tag(v_proof_3733_))
{
case 0:
{
lean_object* v_declName_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_declName_3735_ = lean_ctor_get(v_proof_3733_, 0);
lean_inc(v_declName_3735_);
lean_dec_ref_known(v_proof_3733_, 1);
v___x_3736_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3737_ = l_Lean_MessageData_ofName(v_declName_3735_);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___y_3657_ = v_a_3730_;
v___y_3658_ = v_a_3732_;
v___y_3659_ = v___y_3694_;
v___y_3660_ = v___y_3700_;
v___y_3661_ = v___x_3734_;
v___y_3662_ = v___x_3714_;
v___y_3663_ = v___y_3696_;
v___y_3664_ = v___y_3697_;
v___y_3665_ = v___x_3738_;
goto v___jp_3656_;
}
case 1:
{
lean_object* v_fvarId_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_fvarId_3739_ = lean_ctor_get(v_proof_3733_, 0);
lean_inc(v_fvarId_3739_);
lean_dec_ref_known(v_proof_3733_, 1);
v___x_3740_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3741_ = l_Lean_mkFVar(v_fvarId_3739_);
v___x_3742_ = l_Lean_MessageData_ofExpr(v___x_3741_);
v___x_3743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3740_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___y_3657_ = v_a_3730_;
v___y_3658_ = v_a_3732_;
v___y_3659_ = v___y_3694_;
v___y_3660_ = v___y_3700_;
v___y_3661_ = v___x_3734_;
v___y_3662_ = v___x_3714_;
v___y_3663_ = v___y_3696_;
v___y_3664_ = v___y_3697_;
v___y_3665_ = v___x_3743_;
goto v___jp_3656_;
}
default: 
{
lean_object* v_ref_3744_; lean_object* v_proof_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v_ref_3744_ = lean_ctor_get(v_proof_3733_, 1);
lean_inc(v_ref_3744_);
v_proof_3745_ = lean_ctor_get(v_proof_3733_, 2);
lean_inc_ref(v_proof_3745_);
lean_dec_ref_known(v_proof_3733_, 3);
v___x_3746_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3747_ = l_Lean_MessageData_ofSyntax(v_ref_3744_);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3746_);
lean_ctor_set(v___x_3748_, 1, v___x_3747_);
v___x_3749_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = l_Lean_MessageData_ofExpr(v_proof_3745_);
v___x_3752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3750_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___y_3657_ = v_a_3730_;
v___y_3658_ = v_a_3732_;
v___y_3659_ = v___y_3694_;
v___y_3660_ = v___y_3700_;
v___y_3661_ = v___x_3734_;
v___y_3662_ = v___x_3714_;
v___y_3663_ = v___y_3696_;
v___y_3664_ = v___y_3697_;
v___y_3665_ = v___x_3752_;
goto v___jp_3656_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_dec(v_a_3730_);
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v_info_3643_);
v_a_3753_ = lean_ctor_get(v___x_3731_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3731_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3731_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
lean_dec_ref(v___x_3714_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
v_a_3761_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3729_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3729_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v___x_3714_);
lean_dec(v_val_3709_);
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
v_a_3770_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3718_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3718_);
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
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec(v_a_3708_);
lean_dec_ref(v___y_3706_);
lean_dec(v_goal_3642_);
v___x_3780_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_3643_);
lean_dec_ref(v_info_3643_);
v___x_3781_ = lean_unsigned_to_nat(1u);
v___x_3782_ = lean_mk_empty_array_with_capacity(v___x_3781_);
v___x_3783_ = lean_array_push(v___x_3782_, v___y_3705_);
v___x_3784_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___y_3703_, v___x_3780_, v___x_3783_, v___y_3704_, v___y_3697_, v___y_3700_, v___y_3696_, v___y_3694_);
return v___x_3784_;
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v___y_3703_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
v_a_3785_ = lean_ctor_get(v___y_3707_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___y_3707_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___y_3707_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___y_3707_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
v___jp_3793_:
{
lean_object* v_excessArgs_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_excessArgs_3812_ = lean_ctor_get(v_info_3643_, 2);
lean_inc_ref(v___y_3801_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___y_3801_);
lean_ctor_set(v___x_3813_, 1, v___y_3811_);
v___x_3814_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
lean_inc_ref(v___y_3807_);
v___x_3816_ = l_Lean_indentExpr(v___y_3807_);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
v___x_3819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3817_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = l_Lean_Exception_toMessageData(v___y_3805_);
v___x_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
v___x_3822_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3821_);
lean_ctor_set(v___x_3823_, 1, v___x_3822_);
v___x_3824_ = l_Lean_indentExpr(v___y_3797_);
v___x_3825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3825_, 0, v___x_3823_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
v___x_3826_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3825_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
v___x_3828_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_3643_);
v___x_3829_ = l_Lean_indentExpr(v___x_3828_);
v___x_3830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3827_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
v___x_3831_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3830_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
lean_inc_ref(v_excessArgs_3812_);
v___x_3833_ = lean_array_to_list(v_excessArgs_3812_);
v___x_3834_ = lean_box(0);
v___x_3835_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3833_, v___x_3834_);
v___x_3836_ = l_Lean_MessageData_ofList(v___x_3835_);
v___x_3837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3832_);
lean_ctor_set(v___x_3837_, 1, v___x_3836_);
v___x_3838_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3837_, v___y_3799_, v___y_3803_, v___y_3798_, v___y_3795_);
v___y_3693_ = v___y_3794_;
v___y_3694_ = v___y_3795_;
v___y_3695_ = v___y_3796_;
v___y_3696_ = v___y_3798_;
v___y_3697_ = v___y_3799_;
v___y_3698_ = v___y_3800_;
v___y_3699_ = v___y_3802_;
v___y_3700_ = v___y_3803_;
v___y_3701_ = v___y_3804_;
v___y_3702_ = v___y_3806_;
v___y_3703_ = v___y_3807_;
v___y_3704_ = v___y_3808_;
v___y_3705_ = v___y_3810_;
v___y_3706_ = v___y_3809_;
v___y_3707_ = v___x_3838_;
goto v___jp_3692_;
}
v___jp_3839_:
{
if (v___y_3856_ == 0)
{
lean_object* v___x_3857_; 
lean_dec_ref(v___y_3840_);
lean_inc(v_goal_3642_);
v___x_3857_ = l_Lean_MVarId_getType(v_goal_3642_, v___y_3845_, v___y_3848_, v___y_3844_, v___y_3842_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v_proof_3859_; lean_object* v___x_3860_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
v_proof_3859_ = lean_ctor_get(v___y_3854_, 1);
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
v___y_3794_ = v___y_3841_;
v___y_3795_ = v___y_3842_;
v___y_3796_ = v___y_3843_;
v___y_3797_ = v_a_3858_;
v___y_3798_ = v___y_3844_;
v___y_3799_ = v___y_3845_;
v___y_3800_ = v___y_3846_;
v___y_3801_ = v___x_3860_;
v___y_3802_ = v___y_3847_;
v___y_3803_ = v___y_3848_;
v___y_3804_ = v___y_3849_;
v___y_3805_ = v___y_3850_;
v___y_3806_ = v___y_3851_;
v___y_3807_ = v___y_3852_;
v___y_3808_ = v___y_3853_;
v___y_3809_ = v___y_3855_;
v___y_3810_ = v___y_3854_;
v___y_3811_ = v___x_3864_;
goto v___jp_3793_;
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
v___y_3794_ = v___y_3841_;
v___y_3795_ = v___y_3842_;
v___y_3796_ = v___y_3843_;
v___y_3797_ = v_a_3858_;
v___y_3798_ = v___y_3844_;
v___y_3799_ = v___y_3845_;
v___y_3800_ = v___y_3846_;
v___y_3801_ = v___x_3860_;
v___y_3802_ = v___y_3847_;
v___y_3803_ = v___y_3848_;
v___y_3804_ = v___y_3849_;
v___y_3805_ = v___y_3850_;
v___y_3806_ = v___y_3851_;
v___y_3807_ = v___y_3852_;
v___y_3808_ = v___y_3853_;
v___y_3809_ = v___y_3855_;
v___y_3810_ = v___y_3854_;
v___y_3811_ = v___x_3869_;
goto v___jp_3793_;
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
v___y_3794_ = v___y_3841_;
v___y_3795_ = v___y_3842_;
v___y_3796_ = v___y_3843_;
v___y_3797_ = v_a_3858_;
v___y_3798_ = v___y_3844_;
v___y_3799_ = v___y_3845_;
v___y_3800_ = v___y_3846_;
v___y_3801_ = v___x_3860_;
v___y_3802_ = v___y_3847_;
v___y_3803_ = v___y_3848_;
v___y_3804_ = v___y_3849_;
v___y_3805_ = v___y_3850_;
v___y_3806_ = v___y_3851_;
v___y_3807_ = v___y_3852_;
v___y_3808_ = v___y_3853_;
v___y_3809_ = v___y_3855_;
v___y_3810_ = v___y_3854_;
v___y_3811_ = v___x_3878_;
goto v___jp_3793_;
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_dec_ref(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec_ref(v___y_3852_);
lean_dec_ref(v___y_3850_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
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
lean_dec_ref(v___y_3850_);
v___y_3693_ = v___y_3841_;
v___y_3694_ = v___y_3842_;
v___y_3695_ = v___y_3843_;
v___y_3696_ = v___y_3844_;
v___y_3697_ = v___y_3845_;
v___y_3698_ = v___y_3846_;
v___y_3699_ = v___y_3847_;
v___y_3700_ = v___y_3848_;
v___y_3701_ = v___y_3849_;
v___y_3702_ = v___y_3851_;
v___y_3703_ = v___y_3852_;
v___y_3704_ = v___y_3853_;
v___y_3705_ = v___y_3854_;
v___y_3706_ = v___y_3855_;
v___y_3707_ = v___y_3840_;
goto v___jp_3692_;
}
}
v___jp_3887_:
{
lean_object* v___x_3902_; 
lean_inc_ref(v_info_3643_);
lean_inc_ref(v___y_3890_);
v___x_3902_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v___y_3890_, v_info_3643_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3902_) == 0)
{
v___y_3693_ = v___y_3895_;
v___y_3694_ = v___y_3901_;
v___y_3695_ = v___y_3893_;
v___y_3696_ = v___y_3900_;
v___y_3697_ = v___y_3898_;
v___y_3698_ = v___y_3897_;
v___y_3699_ = v___y_3896_;
v___y_3700_ = v___y_3899_;
v___y_3701_ = v___y_3892_;
v___y_3702_ = v___y_3894_;
v___y_3703_ = v___y_3888_;
v___y_3704_ = v___y_3891_;
v___y_3705_ = v___y_3890_;
v___y_3706_ = v___y_3889_;
v___y_3707_ = v___x_3902_;
goto v___jp_3692_;
}
else
{
lean_object* v_a_3903_; uint8_t v___x_3904_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
v___x_3904_ = l_Lean_Exception_isInterrupt(v_a_3903_);
if (v___x_3904_ == 0)
{
uint8_t v___x_3905_; 
lean_inc(v_a_3903_);
v___x_3905_ = l_Lean_Exception_isRuntime(v_a_3903_);
v___y_3840_ = v___x_3902_;
v___y_3841_ = v___y_3895_;
v___y_3842_ = v___y_3901_;
v___y_3843_ = v___y_3893_;
v___y_3844_ = v___y_3900_;
v___y_3845_ = v___y_3898_;
v___y_3846_ = v___y_3897_;
v___y_3847_ = v___y_3896_;
v___y_3848_ = v___y_3899_;
v___y_3849_ = v___y_3892_;
v___y_3850_ = v_a_3903_;
v___y_3851_ = v___y_3894_;
v___y_3852_ = v___y_3888_;
v___y_3853_ = v___y_3891_;
v___y_3854_ = v___y_3890_;
v___y_3855_ = v___y_3889_;
v___y_3856_ = v___x_3905_;
goto v___jp_3839_;
}
else
{
v___y_3840_ = v___x_3902_;
v___y_3841_ = v___y_3895_;
v___y_3842_ = v___y_3901_;
v___y_3843_ = v___y_3893_;
v___y_3844_ = v___y_3900_;
v___y_3845_ = v___y_3898_;
v___y_3846_ = v___y_3897_;
v___y_3847_ = v___y_3896_;
v___y_3848_ = v___y_3899_;
v___y_3849_ = v___y_3892_;
v___y_3850_ = v_a_3903_;
v___y_3851_ = v___y_3894_;
v___y_3852_ = v___y_3888_;
v___y_3853_ = v___y_3891_;
v___y_3854_ = v___y_3890_;
v___y_3855_ = v___y_3889_;
v___y_3856_ = v___x_3904_;
goto v___jp_3839_;
}
}
}
v___jp_3910_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3927_, 0, v___y_3911_);
lean_ctor_set(v___x_3927_, 1, v___y_3926_);
v___x_3928_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3909_, v___x_3927_, v___y_3923_, v___y_3915_, v___y_3913_, v___y_3919_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_dec_ref_known(v___x_3928_, 1);
v___y_3888_ = v___y_3920_;
v___y_3889_ = v___y_3925_;
v___y_3890_ = v___y_3924_;
v___y_3891_ = v___y_3921_;
v___y_3892_ = v___y_3922_;
v___y_3893_ = v___y_3914_;
v___y_3894_ = v___y_3918_;
v___y_3895_ = v___y_3916_;
v___y_3896_ = v___y_3912_;
v___y_3897_ = v___y_3917_;
v___y_3898_ = v___y_3923_;
v___y_3899_ = v___y_3915_;
v___y_3900_ = v___y_3913_;
v___y_3901_ = v___y_3919_;
goto v___jp_3887_;
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec_ref(v___y_3920_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3928_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3928_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
v___jp_3937_:
{
lean_object* v_specs_3949_; lean_object* v_jps_3950_; lean_object* v_lastLiftedPre_x3f_3951_; lean_object* v_nextDeclIdx_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_4012_; 
v_specs_3949_ = lean_ctor_get(v_scope_3641_, 0);
v_jps_3950_ = lean_ctor_get(v_scope_3641_, 1);
v_lastLiftedPre_x3f_3951_ = lean_ctor_get(v_scope_3641_, 2);
v_nextDeclIdx_3952_ = lean_ctor_get(v_scope_3641_, 3);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_scope_3641_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3954_ = v_scope_3641_;
v_isShared_3955_ = v_isSharedCheck_4012_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_nextDeclIdx_3952_);
lean_inc(v_lastLiftedPre_x3f_3951_);
lean_inc(v_jps_3950_);
lean_inc(v_specs_3949_);
lean_dec(v_scope_3641_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_4012_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3643_);
lean_inc_ref(v___x_3956_);
v___x_3957_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(v_specs_3949_, v___x_3956_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; lean_object* v_fst_3959_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v_fst_3959_ = lean_ctor_get(v_a_3958_, 0);
lean_inc(v_fst_3959_);
if (lean_obj_tag(v_fst_3959_) == 0)
{
lean_object* v_a_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec(v_a_3958_);
lean_del_object(v___x_3954_);
lean_dec(v_nextDeclIdx_3952_);
lean_dec(v_lastLiftedPre_x3f_3951_);
lean_dec(v_jps_3950_);
lean_dec(v_goal_3642_);
v_a_3960_ = lean_ctor_get(v_fst_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v_fst_3959_, 1);
v___x_3961_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_3643_);
lean_dec_ref(v_info_3643_);
v___x_3962_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3956_, v___x_3961_, v_a_3960_, v___y_3938_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3962_;
}
else
{
lean_object* v_options_3963_; lean_object* v_snd_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4002_; 
v_options_3963_ = lean_ctor_get(v___y_3947_, 2);
v_snd_3964_ = lean_ctor_get(v_a_3958_, 1);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_a_3958_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v_a_3958_, 0);
lean_dec(v_unused_4003_);
v___x_3966_ = v_a_3958_;
v_isShared_3967_ = v_isSharedCheck_4002_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_snd_3964_);
lean_dec(v_a_3958_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4002_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v_a_3968_; lean_object* v_inheritedTraceOptions_3969_; uint8_t v_hasTrace_3970_; lean_object* v___x_3972_; 
v_a_3968_ = lean_ctor_get(v_fst_3959_, 0);
lean_inc(v_a_3968_);
lean_dec_ref_known(v_fst_3959_, 1);
v_inheritedTraceOptions_3969_ = lean_ctor_get(v___y_3947_, 13);
v_hasTrace_3970_ = lean_ctor_get_uint8(v_options_3963_, sizeof(void*)*1);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 0, v_snd_3964_);
v___x_3972_ = v___x_3954_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_snd_3964_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_jps_3950_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_lastLiftedPre_x3f_3951_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_nextDeclIdx_3952_);
v___x_3972_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
if (v_hasTrace_3970_ == 0)
{
lean_del_object(v___x_3966_);
v___y_3888_ = v___x_3956_;
v___y_3889_ = v___x_3972_;
v___y_3890_ = v_a_3968_;
v___y_3891_ = v___y_3938_;
v___y_3892_ = v___y_3939_;
v___y_3893_ = v___y_3940_;
v___y_3894_ = v___y_3941_;
v___y_3895_ = v___y_3942_;
v___y_3896_ = v___y_3943_;
v___y_3897_ = v___y_3944_;
v___y_3898_ = v___y_3945_;
v___y_3899_ = v___y_3946_;
v___y_3900_ = v___y_3947_;
v___y_3901_ = v___y_3948_;
goto v___jp_3887_;
}
else
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3969_, v_options_3963_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_del_object(v___x_3966_);
v___y_3888_ = v___x_3956_;
v___y_3889_ = v___x_3972_;
v___y_3890_ = v_a_3968_;
v___y_3891_ = v___y_3938_;
v___y_3892_ = v___y_3939_;
v___y_3893_ = v___y_3940_;
v___y_3894_ = v___y_3941_;
v___y_3895_ = v___y_3942_;
v___y_3896_ = v___y_3943_;
v___y_3897_ = v___y_3944_;
v___y_3898_ = v___y_3945_;
v___y_3899_ = v___y_3946_;
v___y_3900_ = v___y_3947_;
v___y_3901_ = v___y_3948_;
goto v___jp_3887_;
}
else
{
lean_object* v_proof_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v_proof_3975_ = lean_ctor_get(v_a_3968_, 1);
v___x_3976_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
lean_inc_ref(v___x_3956_);
v___x_3977_ = l_Lean_MessageData_ofExpr(v___x_3956_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set_tag(v___x_3966_, 7);
lean_ctor_set(v___x_3966_, 1, v___x_3977_);
lean_ctor_set(v___x_3966_, 0, v___x_3976_);
v___x_3979_ = v___x_3966_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v___x_3976_);
lean_ctor_set(v_reuseFailAlloc_4000_, 1, v___x_3977_);
v___x_3979_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_3981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
switch(lean_obj_tag(v_proof_3975_))
{
case 0:
{
lean_object* v_declName_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v_declName_3982_ = lean_ctor_get(v_proof_3975_, 0);
v___x_3983_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3982_);
v___x_3984_ = l_Lean_MessageData_ofName(v_declName_3982_);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___y_3911_ = v___x_3981_;
v___y_3912_ = v___y_3943_;
v___y_3913_ = v___y_3947_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3946_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3944_;
v___y_3918_ = v___y_3941_;
v___y_3919_ = v___y_3948_;
v___y_3920_ = v___x_3956_;
v___y_3921_ = v___y_3938_;
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___y_3945_;
v___y_3924_ = v_a_3968_;
v___y_3925_ = v___x_3972_;
v___y_3926_ = v___x_3985_;
goto v___jp_3910_;
}
case 1:
{
lean_object* v_fvarId_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; 
v_fvarId_3986_ = lean_ctor_get(v_proof_3975_, 0);
v___x_3987_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3986_);
v___x_3988_ = l_Lean_mkFVar(v_fvarId_3986_);
v___x_3989_ = l_Lean_MessageData_ofExpr(v___x_3988_);
v___x_3990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3987_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___y_3911_ = v___x_3981_;
v___y_3912_ = v___y_3943_;
v___y_3913_ = v___y_3947_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3946_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3944_;
v___y_3918_ = v___y_3941_;
v___y_3919_ = v___y_3948_;
v___y_3920_ = v___x_3956_;
v___y_3921_ = v___y_3938_;
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___y_3945_;
v___y_3924_ = v_a_3968_;
v___y_3925_ = v___x_3972_;
v___y_3926_ = v___x_3990_;
goto v___jp_3910_;
}
default: 
{
lean_object* v_ref_3991_; lean_object* v_proof_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; 
v_ref_3991_ = lean_ctor_get(v_proof_3975_, 1);
v_proof_3992_ = lean_ctor_get(v_proof_3975_, 2);
v___x_3993_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3991_);
v___x_3994_ = l_Lean_MessageData_ofSyntax(v_ref_3991_);
v___x_3995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3993_);
lean_ctor_set(v___x_3995_, 1, v___x_3994_);
v___x_3996_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3995_);
lean_ctor_set(v___x_3997_, 1, v___x_3996_);
lean_inc_ref(v_proof_3992_);
v___x_3998_ = l_Lean_MessageData_ofExpr(v_proof_3992_);
v___x_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3997_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___y_3911_ = v___x_3981_;
v___y_3912_ = v___y_3943_;
v___y_3913_ = v___y_3947_;
v___y_3914_ = v___y_3940_;
v___y_3915_ = v___y_3946_;
v___y_3916_ = v___y_3942_;
v___y_3917_ = v___y_3944_;
v___y_3918_ = v___y_3941_;
v___y_3919_ = v___y_3948_;
v___y_3920_ = v___x_3956_;
v___y_3921_ = v___y_3938_;
v___y_3922_ = v___y_3939_;
v___y_3923_ = v___y_3945_;
v___y_3924_ = v_a_3968_;
v___y_3925_ = v___x_3972_;
v___y_3926_ = v___x_3999_;
goto v___jp_3910_;
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
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v___x_3956_);
lean_del_object(v___x_3954_);
lean_dec(v_nextDeclIdx_3952_);
lean_dec(v_lastLiftedPre_x3f_3951_);
lean_dec(v_jps_3950_);
lean_dec_ref(v_info_3643_);
lean_dec(v_goal_3642_);
v_a_4004_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3957_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3957_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object* v_scope_4036_, lean_object* v_goal_4037_, lean_object* v_info_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_4036_, v_goal_4037_, v_info_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec_ref(v_a_4048_);
lean_dec(v_a_4047_);
lean_dec_ref(v_a_4046_);
lean_dec(v_a_4045_);
lean_dec_ref(v_a_4044_);
lean_dec(v_a_4043_);
lean_dec_ref(v_a_4042_);
lean_dec(v_a_4041_);
lean_dec(v_a_4040_);
lean_dec_ref(v_a_4039_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(lean_object* v_d_4052_, lean_object* v_writeback_4053_, lean_object* v_m_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_){
_start:
{
if (lean_obj_tag(v_d_4052_) == 0)
{
lean_object* v_elabFn_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4093_; 
v_elabFn_4067_ = lean_ctor_get(v_d_4052_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v_d_4052_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4069_ = v_d_4052_;
v_isShared_4070_ = v_isSharedCheck_4093_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_elabFn_4067_);
lean_dec(v_d_4052_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4093_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; 
lean_inc(v___y_4065_);
lean_inc_ref(v___y_4064_);
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4062_);
v___x_4071_ = lean_apply_6(v_elabFn_4067_, v_m_4054_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, lean_box(0));
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4074_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc_n(v_a_4072_, 2);
lean_dec_ref_known(v___x_4071_, 1);
if (v_isShared_4070_ == 0)
{
lean_ctor_set_tag(v___x_4069_, 1);
lean_ctor_set(v___x_4069_, 0, v_a_4072_);
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4092_; 
v_reuseFailAlloc_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4092_, 0, v_a_4072_);
v___x_4074_ = v_reuseFailAlloc_4092_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; 
lean_inc(v___y_4065_);
lean_inc_ref(v___y_4064_);
lean_inc(v___y_4063_);
lean_inc_ref(v___y_4062_);
lean_inc(v___y_4061_);
lean_inc_ref(v___y_4060_);
lean_inc(v___y_4059_);
lean_inc_ref(v___y_4058_);
lean_inc(v___y_4057_);
lean_inc(v___y_4056_);
lean_inc_ref(v___y_4055_);
v___x_4075_ = lean_apply_13(v_writeback_4053_, v___x_4074_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_, lean_box(0));
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4075_);
if (v_isSharedCheck_4082_ == 0)
{
lean_object* v_unused_4083_; 
v_unused_4083_ = lean_ctor_get(v___x_4075_, 0);
lean_dec(v_unused_4083_);
v___x_4077_ = v___x_4075_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_dec(v___x_4075_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
lean_ctor_set(v___x_4077_, 0, v_a_4072_);
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4072_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
else
{
lean_object* v_a_4084_; lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4091_; 
lean_dec(v_a_4072_);
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
else
{
lean_del_object(v___x_4069_);
lean_dec_ref(v_writeback_4053_);
return v___x_4071_;
}
}
}
else
{
lean_object* v_value_4094_; lean_object* v___x_4095_; 
lean_dec_ref(v_m_4054_);
lean_dec_ref(v_writeback_4053_);
v_value_4094_ = lean_ctor_get(v_d_4052_, 0);
lean_inc(v_value_4094_);
lean_dec_ref_known(v_d_4052_, 1);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_value_4094_);
return v___x_4095_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg___boxed(lean_object* v_d_4096_, lean_object* v_writeback_4097_, lean_object* v_m_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_){
_start:
{
lean_object* v_res_4111_; 
v_res_4111_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v_d_4096_, v_writeback_4097_, v_m_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec(v___y_4109_);
lean_dec_ref(v___y_4108_);
lean_dec(v___y_4107_);
lean_dec_ref(v___y_4106_);
lean_dec(v___y_4105_);
lean_dec_ref(v___y_4104_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec(v___y_4100_);
lean_dec_ref(v___y_4099_);
return v_res_4111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0(lean_object* v_00_u03b1_4112_, lean_object* v_d_4113_, lean_object* v_writeback_4114_, lean_object* v_m_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v_d_4113_, v_writeback_4114_, v_m_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___boxed(lean_object* v_00_u03b1_4129_, lean_object* v_d_4130_, lean_object* v_writeback_4131_, lean_object* v_m_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v_res_4145_; 
v_res_4145_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0(v_00_u03b1_4129_, v_d_4130_, v_writeback_4131_, v_m_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
lean_dec(v___y_4143_);
lean_dec_ref(v___y_4142_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
lean_dec_ref(v___y_4138_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0(lean_object* v_val_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4160_ = lean_st_ref_set(v_val_4146_, v___y_4147_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
return v___x_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0___boxed(lean_object* v_val_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0(v_val_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec(v___y_4165_);
lean_dec_ref(v___y_4164_);
lean_dec(v_val_4162_);
return v_res_4176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__0));
v___x_4179_ = l_Lean_stringToMessageData(v___x_4178_);
return v___x_4179_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4181_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__2));
v___x_4182_ = l_Lean_stringToMessageData(v___x_4181_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object* v_m_4183_, lean_object* v_prog_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v_untilPat_x3f_4197_; 
v_untilPat_x3f_4197_ = lean_ctor_get(v_a_4185_, 3);
if (lean_obj_tag(v_untilPat_x3f_4197_) == 1)
{
lean_object* v_val_4198_; lean_object* v___x_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; 
v_val_4198_ = lean_ctor_get(v_untilPat_x3f_4197_, 0);
v___x_4199_ = lean_st_ref_get(v_val_4198_);
lean_inc(v_val_4198_);
v___f_4200_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___lam__0___boxed), 14, 1);
lean_closure_set(v___f_4200_, 0, v_val_4198_);
v___x_4201_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v___x_4199_, v___f_4200_, v_m_4183_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; uint8_t v___x_4203_; lean_object* v___x_4204_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4201_, 1);
v___x_4203_ = 1;
lean_inc_ref(v_prog_4184_);
v___x_4204_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_a_4202_, v_prog_4184_, v___x_4203_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4251_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4207_ = v___x_4204_;
v_isShared_4208_ = v_isSharedCheck_4251_;
goto v_resetjp_4206_;
}
else
{
lean_inc(v_a_4205_);
lean_dec(v___x_4204_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4251_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
if (lean_obj_tag(v_a_4205_) == 0)
{
uint8_t v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4212_; 
lean_dec_ref(v_prog_4184_);
v___x_4209_ = 0;
v___x_4210_ = lean_box(v___x_4209_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4210_);
v___x_4212_ = v___x_4207_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v___x_4210_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
else
{
lean_object* v_options_4214_; uint8_t v_hasTrace_4215_; 
lean_dec_ref_known(v_a_4205_, 1);
v_options_4214_ = lean_ctor_get(v_a_4194_, 2);
v_hasTrace_4215_ = lean_ctor_get_uint8(v_options_4214_, sizeof(void*)*1);
if (v_hasTrace_4215_ == 0)
{
lean_object* v___x_4216_; lean_object* v___x_4218_; 
lean_dec_ref(v_prog_4184_);
v___x_4216_ = lean_box(v___x_4203_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4216_);
v___x_4218_ = v___x_4207_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___x_4216_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
else
{
lean_object* v_inheritedTraceOptions_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; uint8_t v___x_4223_; 
v_inheritedTraceOptions_4220_ = lean_ctor_get(v_a_4194_, 13);
v___x_4221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_4222_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4220_, v_options_4214_, v___x_4222_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; lean_object* v___x_4226_; 
lean_dec_ref(v_prog_4184_);
v___x_4224_ = lean_box(v___x_4203_);
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v___x_4224_);
v___x_4226_ = v___x_4207_;
goto v_reusejp_4225_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___x_4224_);
v___x_4226_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4225_;
}
v_reusejp_4225_:
{
return v___x_4226_;
}
}
else
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_del_object(v___x_4207_);
v___x_4228_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__1);
v___x_4229_ = l_Lean_MessageData_ofExpr(v_prog_4184_);
v___x_4230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4228_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___closed__3);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4221_, v___x_4232_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4241_; 
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4241_ == 0)
{
lean_object* v_unused_4242_; 
v_unused_4242_ = lean_ctor_get(v___x_4233_, 0);
lean_dec(v_unused_4242_);
v___x_4235_ = v___x_4233_;
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
else
{
lean_dec(v___x_4233_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4241_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; lean_object* v___x_4239_; 
v___x_4237_ = lean_box(v___x_4203_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v___x_4237_);
v___x_4239_ = v___x_4235_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v___x_4237_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v_a_4243_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4233_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4233_);
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
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec_ref(v_prog_4184_);
v_a_4252_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4204_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4204_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_dec_ref(v_prog_4184_);
v_a_4260_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4201_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4201_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
uint8_t v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_dec_ref(v_prog_4184_);
lean_dec_ref(v_m_4183_);
v___x_4268_ = 0;
v___x_4269_ = lean_box(v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4269_);
return v___x_4270_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object* v_m_4271_, lean_object* v_prog_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_){
_start:
{
lean_object* v_res_4285_; 
v_res_4285_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v_m_4271_, v_prog_4272_, v_a_4273_, v_a_4274_, v_a_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_, v_a_4283_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(lean_object* v_k_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v_b_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; 
lean_inc(v___y_4298_);
lean_inc_ref(v___y_4297_);
lean_inc(v___y_4296_);
lean_inc_ref(v___y_4295_);
lean_inc(v___y_4293_);
lean_inc_ref(v___y_4292_);
lean_inc(v___y_4291_);
lean_inc_ref(v___y_4290_);
lean_inc(v___y_4289_);
lean_inc(v___y_4288_);
lean_inc_ref(v___y_4287_);
v___x_4300_ = lean_apply_13(v_k_4286_, v_b_4294_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, lean_box(0));
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed(lean_object* v_k_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v_b_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0(v_k_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v_b_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(lean_object* v_name_4316_, lean_object* v_type_4317_, lean_object* v_val_4318_, lean_object* v_k_4319_, uint8_t v_nondep_4320_, uint8_t v_kind_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_){
_start:
{
lean_object* v___f_4334_; lean_object* v___x_4335_; 
lean_inc(v___y_4328_);
lean_inc_ref(v___y_4327_);
lean_inc(v___y_4326_);
lean_inc_ref(v___y_4325_);
lean_inc(v___y_4324_);
lean_inc(v___y_4323_);
lean_inc_ref(v___y_4322_);
v___f_4334_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___lam__0___boxed), 14, 8);
lean_closure_set(v___f_4334_, 0, v_k_4319_);
lean_closure_set(v___f_4334_, 1, v___y_4322_);
lean_closure_set(v___f_4334_, 2, v___y_4323_);
lean_closure_set(v___f_4334_, 3, v___y_4324_);
lean_closure_set(v___f_4334_, 4, v___y_4325_);
lean_closure_set(v___f_4334_, 5, v___y_4326_);
lean_closure_set(v___f_4334_, 6, v___y_4327_);
lean_closure_set(v___f_4334_, 7, v___y_4328_);
v___x_4335_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_4316_, v_type_4317_, v_val_4318_, v___f_4334_, v_nondep_4320_, v_kind_4321_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
if (lean_obj_tag(v___x_4335_) == 0)
{
return v___x_4335_;
}
else
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg___boxed(lean_object** _args){
lean_object* v_name_4344_ = _args[0];
lean_object* v_type_4345_ = _args[1];
lean_object* v_val_4346_ = _args[2];
lean_object* v_k_4347_ = _args[3];
lean_object* v_nondep_4348_ = _args[4];
lean_object* v_kind_4349_ = _args[5];
lean_object* v___y_4350_ = _args[6];
lean_object* v___y_4351_ = _args[7];
lean_object* v___y_4352_ = _args[8];
lean_object* v___y_4353_ = _args[9];
lean_object* v___y_4354_ = _args[10];
lean_object* v___y_4355_ = _args[11];
lean_object* v___y_4356_ = _args[12];
lean_object* v___y_4357_ = _args[13];
lean_object* v___y_4358_ = _args[14];
lean_object* v___y_4359_ = _args[15];
lean_object* v___y_4360_ = _args[16];
lean_object* v___y_4361_ = _args[17];
_start:
{
uint8_t v_nondep_boxed_4362_; uint8_t v_kind_boxed_4363_; lean_object* v_res_4364_; 
v_nondep_boxed_4362_ = lean_unbox(v_nondep_4348_);
v_kind_boxed_4363_ = lean_unbox(v_kind_4349_);
v_res_4364_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4344_, v_type_4345_, v_val_4346_, v_k_4347_, v_nondep_boxed_4362_, v_kind_boxed_4363_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
lean_dec(v___y_4352_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
return v_res_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(lean_object* v_00_u03b1_4365_, lean_object* v_name_4366_, lean_object* v_type_4367_, lean_object* v_val_4368_, lean_object* v_k_4369_, uint8_t v_nondep_4370_, uint8_t v_kind_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_){
_start:
{
lean_object* v___x_4384_; 
v___x_4384_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_name_4366_, v_type_4367_, v_val_4368_, v_k_4369_, v_nondep_4370_, v_kind_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
return v___x_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___boxed(lean_object** _args){
lean_object* v_00_u03b1_4385_ = _args[0];
lean_object* v_name_4386_ = _args[1];
lean_object* v_type_4387_ = _args[2];
lean_object* v_val_4388_ = _args[3];
lean_object* v_k_4389_ = _args[4];
lean_object* v_nondep_4390_ = _args[5];
lean_object* v_kind_4391_ = _args[6];
lean_object* v___y_4392_ = _args[7];
lean_object* v___y_4393_ = _args[8];
lean_object* v___y_4394_ = _args[9];
lean_object* v___y_4395_ = _args[10];
lean_object* v___y_4396_ = _args[11];
lean_object* v___y_4397_ = _args[12];
lean_object* v___y_4398_ = _args[13];
lean_object* v___y_4399_ = _args[14];
lean_object* v___y_4400_ = _args[15];
lean_object* v___y_4401_ = _args[16];
lean_object* v___y_4402_ = _args[17];
lean_object* v___y_4403_ = _args[18];
_start:
{
uint8_t v_nondep_boxed_4404_; uint8_t v_kind_boxed_4405_; lean_object* v_res_4406_; 
v_nondep_boxed_4404_ = lean_unbox(v_nondep_4390_);
v_kind_boxed_4405_ = lean_unbox(v_kind_4391_);
v_res_4406_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0(v_00_u03b1_4385_, v_name_4386_, v_type_4387_, v_val_4388_, v_k_4389_, v_nondep_boxed_4404_, v_kind_boxed_4405_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed(lean_object* v_acc_4407_, lean_object* v_declInfos_4408_, lean_object* v_k_4409_, lean_object* v_fv_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(v_acc_4407_, v_declInfos_4408_, v_k_4409_, v_fv_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v___y_4417_);
lean_dec_ref(v___y_4416_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec_ref(v___y_4411_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(lean_object* v_declInfos_4424_, lean_object* v_k_4425_, lean_object* v_acc_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_, lean_object* v_a_4437_){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4439_ = lean_array_get_size(v_acc_4426_);
v___x_4440_ = lean_array_get_size(v_declInfos_4424_);
v___x_4441_ = lean_nat_dec_lt(v___x_4439_, v___x_4440_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; 
lean_dec_ref(v_declInfos_4424_);
lean_inc(v_a_4437_);
lean_inc_ref(v_a_4436_);
lean_inc(v_a_4435_);
lean_inc_ref(v_a_4434_);
lean_inc(v_a_4433_);
lean_inc_ref(v_a_4432_);
lean_inc(v_a_4431_);
lean_inc_ref(v_a_4430_);
lean_inc(v_a_4429_);
lean_inc(v_a_4428_);
lean_inc_ref(v_a_4427_);
v___x_4442_ = lean_apply_13(v_k_4425_, v_acc_4426_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_, lean_box(0));
return v___x_4442_;
}
else
{
lean_object* v___x_4443_; lean_object* v_snd_4444_; lean_object* v_fst_4445_; lean_object* v_fst_4446_; lean_object* v_snd_4447_; lean_object* v___f_4448_; uint8_t v___x_4449_; uint8_t v___x_4450_; lean_object* v___x_4451_; 
v___x_4443_ = lean_array_fget_borrowed(v_declInfos_4424_, v___x_4439_);
v_snd_4444_ = lean_ctor_get(v___x_4443_, 1);
v_fst_4445_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_fst_4445_);
v_fst_4446_ = lean_ctor_get(v_snd_4444_, 0);
lean_inc(v_fst_4446_);
v_snd_4447_ = lean_ctor_get(v_snd_4444_, 1);
lean_inc(v_snd_4447_);
v___f_4448_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0___boxed), 16, 3);
lean_closure_set(v___f_4448_, 0, v_acc_4426_);
lean_closure_set(v___f_4448_, 1, v_declInfos_4424_);
lean_closure_set(v___f_4448_, 2, v_k_4425_);
v___x_4449_ = 0;
v___x_4450_ = 0;
v___x_4451_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_spec__0___redArg(v_fst_4445_, v_fst_4446_, v_snd_4447_, v___f_4448_, v___x_4449_, v___x_4450_, v_a_4427_, v_a_4428_, v_a_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_, v_a_4437_);
return v___x_4451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___lam__0(lean_object* v_acc_4452_, lean_object* v_declInfos_4453_, lean_object* v_k_4454_, lean_object* v_fv_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = lean_array_push(v_acc_4452_, v_fv_4455_);
v___x_4469_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4453_, v_k_4454_, v___x_4468_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
return v___x_4469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop___boxed(lean_object* v_declInfos_4470_, lean_object* v_k_4471_, lean_object* v_acc_4472_, lean_object* v_a_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_, lean_object* v_a_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4470_, v_k_4471_, v_acc_4472_, v_a_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_, v_a_4480_, v_a_4481_, v_a_4482_, v_a_4483_);
lean_dec(v_a_4483_);
lean_dec_ref(v_a_4482_);
lean_dec(v_a_4481_);
lean_dec_ref(v_a_4480_);
lean_dec(v_a_4479_);
lean_dec_ref(v_a_4478_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec(v_a_4474_);
lean_dec_ref(v_a_4473_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter___redArg(lean_object* v_x_4486_, lean_object* v_h__1_4487_){
_start:
{
lean_object* v_snd_4488_; lean_object* v_fst_4489_; lean_object* v_fst_4490_; lean_object* v_snd_4491_; lean_object* v___x_4492_; 
v_snd_4488_ = lean_ctor_get(v_x_4486_, 1);
lean_inc(v_snd_4488_);
v_fst_4489_ = lean_ctor_get(v_x_4486_, 0);
lean_inc(v_fst_4489_);
lean_dec_ref(v_x_4486_);
v_fst_4490_ = lean_ctor_get(v_snd_4488_, 0);
lean_inc(v_fst_4490_);
v_snd_4491_ = lean_ctor_get(v_snd_4488_, 1);
lean_inc(v_snd_4491_);
lean_dec(v_snd_4488_);
v___x_4492_ = lean_apply_3(v_h__1_4487_, v_fst_4489_, v_fst_4490_, v_snd_4491_);
return v___x_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop_match__1_splitter(lean_object* v_motive_4493_, lean_object* v_x_4494_, lean_object* v_h__1_4495_){
_start:
{
lean_object* v_snd_4496_; lean_object* v_fst_4497_; lean_object* v_fst_4498_; lean_object* v_snd_4499_; lean_object* v___x_4500_; 
v_snd_4496_ = lean_ctor_get(v_x_4494_, 1);
lean_inc(v_snd_4496_);
v_fst_4497_ = lean_ctor_get(v_x_4494_, 0);
lean_inc(v_fst_4497_);
lean_dec_ref(v_x_4494_);
v_fst_4498_ = lean_ctor_get(v_snd_4496_, 0);
lean_inc(v_fst_4498_);
v_snd_4499_ = lean_ctor_get(v_snd_4496_, 1);
lean_inc(v_snd_4499_);
lean_dec(v_snd_4496_);
v___x_4500_ = lean_apply_3(v_h__1_4495_, v_fst_4497_, v_fst_4498_, v_snd_4499_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(lean_object* v_declInfos_4503_, lean_object* v_k_4504_, lean_object* v_a_4505_, lean_object* v_a_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___closed__0));
v___x_4518_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_declInfos_4503_, v_k_4504_, v___x_4517_, v_a_4505_, v_a_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_, v_a_4515_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND___boxed(lean_object* v_declInfos_4519_, lean_object* v_k_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND(v_declInfos_4519_, v_k_4520_, v_a_4521_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_, v_a_4530_, v_a_4531_);
lean_dec(v_a_4531_);
lean_dec_ref(v_a_4530_);
lean_dec(v_a_4529_);
lean_dec_ref(v_a_4528_);
lean_dec(v_a_4527_);
lean_dec_ref(v_a_4526_);
lean_dec(v_a_4525_);
lean_dec_ref(v_a_4524_);
lean_dec(v_a_4523_);
lean_dec(v_a_4522_);
lean_dec_ref(v_a_4521_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(lean_object* v_e_4534_, lean_object* v___y_4535_){
_start:
{
uint8_t v___x_4537_; uint8_t v___x_4538_; 
v___x_4537_ = l_Lean_Expr_hasMVar(v_e_4534_);
v___x_4538_ = lean_bool_not(v___x_4537_);
if (v___x_4538_ == 0)
{
lean_object* v___x_4539_; lean_object* v_mctx_4540_; lean_object* v___x_4541_; lean_object* v_fst_4542_; lean_object* v_snd_4543_; lean_object* v___x_4544_; lean_object* v_cache_4545_; lean_object* v_zetaDeltaFVarIds_4546_; lean_object* v_postponed_4547_; lean_object* v_diag_4548_; lean_object* v___x_4550_; uint8_t v_isShared_4551_; uint8_t v_isSharedCheck_4557_; 
v___x_4539_ = lean_st_ref_get(v___y_4535_);
v_mctx_4540_ = lean_ctor_get(v___x_4539_, 0);
lean_inc_ref(v_mctx_4540_);
lean_dec(v___x_4539_);
v___x_4541_ = l_Lean_instantiateMVarsCore(v_mctx_4540_, v_e_4534_);
v_fst_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_fst_4542_);
v_snd_4543_ = lean_ctor_get(v___x_4541_, 1);
lean_inc(v_snd_4543_);
lean_dec_ref(v___x_4541_);
v___x_4544_ = lean_st_ref_take(v___y_4535_);
v_cache_4545_ = lean_ctor_get(v___x_4544_, 1);
v_zetaDeltaFVarIds_4546_ = lean_ctor_get(v___x_4544_, 2);
v_postponed_4547_ = lean_ctor_get(v___x_4544_, 3);
v_diag_4548_ = lean_ctor_get(v___x_4544_, 4);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4557_ == 0)
{
lean_object* v_unused_4558_; 
v_unused_4558_ = lean_ctor_get(v___x_4544_, 0);
lean_dec(v_unused_4558_);
v___x_4550_ = v___x_4544_;
v_isShared_4551_ = v_isSharedCheck_4557_;
goto v_resetjp_4549_;
}
else
{
lean_inc(v_diag_4548_);
lean_inc(v_postponed_4547_);
lean_inc(v_zetaDeltaFVarIds_4546_);
lean_inc(v_cache_4545_);
lean_dec(v___x_4544_);
v___x_4550_ = lean_box(0);
v_isShared_4551_ = v_isSharedCheck_4557_;
goto v_resetjp_4549_;
}
v_resetjp_4549_:
{
lean_object* v___x_4553_; 
if (v_isShared_4551_ == 0)
{
lean_ctor_set(v___x_4550_, 0, v_snd_4543_);
v___x_4553_ = v___x_4550_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_snd_4543_);
lean_ctor_set(v_reuseFailAlloc_4556_, 1, v_cache_4545_);
lean_ctor_set(v_reuseFailAlloc_4556_, 2, v_zetaDeltaFVarIds_4546_);
lean_ctor_set(v_reuseFailAlloc_4556_, 3, v_postponed_4547_);
lean_ctor_set(v_reuseFailAlloc_4556_, 4, v_diag_4548_);
v___x_4553_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4554_ = lean_st_ref_set(v___y_4535_, v___x_4553_);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v_fst_4542_);
return v___x_4555_;
}
}
}
else
{
lean_object* v___x_4559_; 
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v_e_4534_);
return v___x_4559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg___boxed(lean_object* v_e_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_e_4560_, v___y_4561_);
lean_dec(v___y_4561_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(lean_object* v_e_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v___x_4572_; 
v___x_4572_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_e_4564_, v___y_4568_);
return v___x_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___boxed(lean_object* v_e_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v_res_4581_; 
v_res_4581_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0(v_e_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4581_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(lean_object* v_x_4582_){
_start:
{
uint8_t v___x_4583_; 
v___x_4583_ = 0;
return v___x_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0___boxed(lean_object* v_x_4584_){
_start:
{
uint8_t v_res_4585_; lean_object* v_r_4586_; 
v_res_4585_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__0(v_x_4584_);
lean_dec(v_x_4584_);
v_r_4586_ = lean_box(v_res_4585_);
return v_r_4586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(lean_object* v_frameStx_4587_, lean_object* v___x_4588_, uint8_t v___x_4589_, lean_object* v___x_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v___x_4598_; 
v___x_4598_ = l_Lean_Elab_Term_elabTermEnsuringType(v_frameStx_4587_, v___x_4588_, v___x_4589_, v___x_4589_, v___x_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; uint8_t v___x_4600_; lean_object* v___x_4601_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref_known(v___x_4598_, 1);
v___x_4600_ = 0;
v___x_4601_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(v___x_4600_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_, v___y_4596_);
if (lean_obj_tag(v___x_4601_) == 0)
{
lean_object* v___x_4602_; 
lean_dec_ref_known(v___x_4601_, 1);
v___x_4602_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__0___redArg(v_a_4599_, v___y_4594_);
return v___x_4602_;
}
else
{
lean_object* v_a_4603_; lean_object* v___x_4605_; uint8_t v_isShared_4606_; uint8_t v_isSharedCheck_4610_; 
lean_dec(v_a_4599_);
v_a_4603_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4610_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4605_ = v___x_4601_;
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
else
{
lean_inc(v_a_4603_);
lean_dec(v___x_4601_);
v___x_4605_ = lean_box(0);
v_isShared_4606_ = v_isSharedCheck_4610_;
goto v_resetjp_4604_;
}
v_resetjp_4604_:
{
lean_object* v___x_4608_; 
if (v_isShared_4606_ == 0)
{
v___x_4608_ = v___x_4605_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_a_4603_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
}
else
{
return v___x_4598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed(lean_object* v_frameStx_4611_, lean_object* v___x_4612_, lean_object* v___x_4613_, lean_object* v___x_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_){
_start:
{
uint8_t v___x_13999__boxed_4622_; lean_object* v_res_4623_; 
v___x_13999__boxed_4622_ = lean_unbox(v___x_4613_);
v_res_4623_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1(v_frameStx_4611_, v___x_4612_, v___x_13999__boxed_4622_, v___x_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(lean_object* v_info_4629_, lean_object* v_frameStx_4630_, lean_object* v___f_4631_, lean_object* v_fvs_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; uint8_t v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___f_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4645_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_4629_);
v___x_4646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4645_);
v___x_4647_ = 1;
v___x_4648_ = lean_box(0);
v___x_4649_ = lean_box(v___x_4647_);
v___f_4650_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4650_, 0, v_frameStx_4630_);
lean_closure_set(v___f_4650_, 1, v___x_4646_);
lean_closure_set(v___f_4650_, 2, v___x_4649_);
lean_closure_set(v___f_4650_, 3, v___x_4648_);
v___x_4651_ = lean_box(0);
v___x_4652_ = lean_box(1);
v___x_4653_ = 0;
v___x_4654_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__0));
v___x_4655_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4655_, 0, v___x_4648_);
lean_ctor_set(v___x_4655_, 1, v___x_4651_);
lean_ctor_set(v___x_4655_, 2, v___x_4648_);
lean_ctor_set(v___x_4655_, 3, v___f_4631_);
lean_ctor_set(v___x_4655_, 4, v___x_4652_);
lean_ctor_set(v___x_4655_, 5, v___x_4652_);
lean_ctor_set(v___x_4655_, 6, v___x_4648_);
lean_ctor_set(v___x_4655_, 7, v___x_4654_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8, v___x_4647_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 1, v___x_4647_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 2, v___x_4647_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 3, v___x_4647_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 4, v___x_4653_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 5, v___x_4653_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 6, v___x_4653_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 7, v___x_4653_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 8, v___x_4647_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 9, v___x_4653_);
lean_ctor_set_uint8(v___x_4655_, sizeof(void*)*8 + 10, v___x_4647_);
v___x_4656_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___closed__1));
v___x_4657_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___f_4650_, v___x_4655_, v___x_4656_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_object* v_a_4658_; lean_object* v_fst_4659_; uint8_t v___x_4660_; lean_object* v___x_4661_; 
v_a_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc(v_a_4658_);
lean_dec_ref_known(v___x_4657_, 1);
v_fst_4659_ = lean_ctor_get(v_a_4658_, 0);
lean_inc(v_fst_4659_);
lean_dec(v_a_4658_);
v___x_4660_ = 1;
v___x_4661_ = l_Lean_Meta_mkLetFVars(v_fvs_4632_, v_fst_4659_, v___x_4647_, v___x_4647_, v___x_4660_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v___x_4661_;
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
v_a_4662_ = lean_ctor_get(v___x_4657_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4657_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4657_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed(lean_object* v_info_4670_, lean_object* v_frameStx_4671_, lean_object* v___f_4672_, lean_object* v_fvs_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v_res_4686_; 
v_res_4686_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2(v_info_4670_, v_frameStx_4671_, v___f_4672_, v_fvs_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_);
lean_dec(v___y_4684_);
lean_dec_ref(v___y_4683_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec_ref(v_fvs_4673_);
lean_dec_ref(v_info_4670_);
return v_res_4686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(lean_object* v___x_4687_, lean_object* v_res_4688_, lean_object* v_range_4689_, lean_object* v_b_4690_, lean_object* v_i_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_stop_4697_; lean_object* v_step_4698_; lean_object* v_a_4700_; uint8_t v___x_4703_; 
v_stop_4697_ = lean_ctor_get(v_range_4689_, 1);
v_step_4698_ = lean_ctor_get(v_range_4689_, 2);
v___x_4703_ = lean_nat_dec_lt(v_i_4691_, v_stop_4697_);
if (v___x_4703_ == 0)
{
lean_object* v___x_4704_; 
lean_dec(v_i_4691_);
v___x_4704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4704_, 0, v_b_4690_);
return v___x_4704_;
}
else
{
lean_object* v___x_4705_; 
v___x_4705_ = lean_array_fget_borrowed(v___x_4687_, v_i_4691_);
if (lean_obj_tag(v___x_4705_) == 1)
{
lean_object* v_val_4706_; lean_object* v_args_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v_val_4706_ = lean_ctor_get(v___x_4705_, 0);
v_args_4707_ = lean_ctor_get(v_res_4688_, 1);
v___x_4708_ = lean_array_get_size(v_args_4707_);
v___x_4709_ = lean_nat_dec_lt(v_i_4691_, v___x_4708_);
if (v___x_4709_ == 0)
{
v_a_4700_ = v_b_4690_;
goto v___jp_4699_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4710_ = l_Lean_instInhabitedExpr;
v___x_4711_ = lean_array_get_borrowed(v___x_4710_, v_args_4707_, v_i_4691_);
lean_inc(v___y_4695_);
lean_inc_ref(v___y_4694_);
lean_inc(v___y_4693_);
lean_inc_ref(v___y_4692_);
lean_inc(v___x_4711_);
v___x_4712_ = lean_infer_type(v___x_4711_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
lean_inc(v_a_4713_);
lean_dec_ref_known(v___x_4712_, 1);
lean_inc(v___x_4711_);
v___x_4714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4714_, 0, v_a_4713_);
lean_ctor_set(v___x_4714_, 1, v___x_4711_);
lean_inc(v_val_4706_);
v___x_4715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4715_, 0, v_val_4706_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = lean_array_push(v_b_4690_, v___x_4715_);
v_a_4700_ = v___x_4716_;
goto v___jp_4699_;
}
else
{
lean_object* v_a_4717_; lean_object* v___x_4719_; uint8_t v_isShared_4720_; uint8_t v_isSharedCheck_4724_; 
lean_dec(v_i_4691_);
lean_dec_ref(v_b_4690_);
v_a_4717_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4724_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4724_ == 0)
{
v___x_4719_ = v___x_4712_;
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
else
{
lean_inc(v_a_4717_);
lean_dec(v___x_4712_);
v___x_4719_ = lean_box(0);
v_isShared_4720_ = v_isSharedCheck_4724_;
goto v_resetjp_4718_;
}
v_resetjp_4718_:
{
lean_object* v___x_4722_; 
if (v_isShared_4720_ == 0)
{
v___x_4722_ = v___x_4719_;
goto v_reusejp_4721_;
}
else
{
lean_object* v_reuseFailAlloc_4723_; 
v_reuseFailAlloc_4723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_a_4717_);
v___x_4722_ = v_reuseFailAlloc_4723_;
goto v_reusejp_4721_;
}
v_reusejp_4721_:
{
return v___x_4722_;
}
}
}
}
}
else
{
v_a_4700_ = v_b_4690_;
goto v___jp_4699_;
}
}
v___jp_4699_:
{
lean_object* v___x_4701_; 
v___x_4701_ = lean_nat_add(v_i_4691_, v_step_4698_);
lean_dec(v_i_4691_);
v_b_4690_ = v_a_4700_;
v_i_4691_ = v___x_4701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg___boxed(lean_object* v___x_4725_, lean_object* v_res_4726_, lean_object* v_range_4727_, lean_object* v_b_4728_, lean_object* v_i_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(v___x_4725_, v_res_4726_, v_range_4727_, v_b_4728_, v_i_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
lean_dec(v___y_4733_);
lean_dec_ref(v___y_4732_);
lean_dec(v___y_4731_);
lean_dec_ref(v___y_4730_);
lean_dec_ref(v_range_4727_);
lean_dec_ref(v_res_4726_);
lean_dec_ref(v___x_4725_);
return v_res_4735_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2(void){
_start:
{
uint8_t v___x_4739_; uint64_t v___x_4740_; 
v___x_4739_ = 1;
v___x_4740_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4739_);
return v___x_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(lean_object* v_entry_4741_, lean_object* v_res_4742_, lean_object* v_info_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v_varNames_4756_; lean_object* v_frameStx_4757_; lean_object* v___x_4758_; lean_object* v_decls_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v_varNames_4756_ = lean_ctor_get(v_entry_4741_, 1);
lean_inc_ref(v_varNames_4756_);
v_frameStx_4757_ = lean_ctor_get(v_entry_4741_, 2);
lean_inc(v_frameStx_4757_);
lean_dec_ref(v_entry_4741_);
v___x_4758_ = lean_unsigned_to_nat(0u);
v_decls_4759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__0));
v___x_4760_ = lean_array_get_size(v_varNames_4756_);
v___x_4761_ = lean_unsigned_to_nat(1u);
v___x_4762_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4758_);
lean_ctor_set(v___x_4762_, 1, v___x_4760_);
lean_ctor_set(v___x_4762_, 2, v___x_4761_);
v___x_4763_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(v_varNames_4756_, v_res_4742_, v___x_4762_, v_decls_4759_, v___x_4758_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
lean_dec_ref_known(v___x_4762_, 3);
lean_dec_ref(v_varNames_4756_);
if (lean_obj_tag(v___x_4763_) == 0)
{
lean_object* v_a_4764_; lean_object* v___x_4765_; uint8_t v_foApprox_4766_; uint8_t v_ctxApprox_4767_; uint8_t v_quasiPatternApprox_4768_; uint8_t v_constApprox_4769_; uint8_t v_isDefEqStuckEx_4770_; uint8_t v_unificationHints_4771_; uint8_t v_proofIrrelevance_4772_; uint8_t v_assignSyntheticOpaque_4773_; uint8_t v_offsetCnstrs_4774_; uint8_t v_etaStruct_4775_; uint8_t v_univApprox_4776_; uint8_t v_iota_4777_; uint8_t v_beta_4778_; uint8_t v_proj_4779_; uint8_t v_zeta_4780_; uint8_t v_zetaDelta_4781_; uint8_t v_zetaUnused_4782_; uint8_t v_zetaHave_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4820_; 
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
lean_inc(v_a_4764_);
lean_dec_ref_known(v___x_4763_, 1);
v___x_4765_ = l_Lean_Meta_Context_config(v_a_4751_);
v_foApprox_4766_ = lean_ctor_get_uint8(v___x_4765_, 0);
v_ctxApprox_4767_ = lean_ctor_get_uint8(v___x_4765_, 1);
v_quasiPatternApprox_4768_ = lean_ctor_get_uint8(v___x_4765_, 2);
v_constApprox_4769_ = lean_ctor_get_uint8(v___x_4765_, 3);
v_isDefEqStuckEx_4770_ = lean_ctor_get_uint8(v___x_4765_, 4);
v_unificationHints_4771_ = lean_ctor_get_uint8(v___x_4765_, 5);
v_proofIrrelevance_4772_ = lean_ctor_get_uint8(v___x_4765_, 6);
v_assignSyntheticOpaque_4773_ = lean_ctor_get_uint8(v___x_4765_, 7);
v_offsetCnstrs_4774_ = lean_ctor_get_uint8(v___x_4765_, 8);
v_etaStruct_4775_ = lean_ctor_get_uint8(v___x_4765_, 10);
v_univApprox_4776_ = lean_ctor_get_uint8(v___x_4765_, 11);
v_iota_4777_ = lean_ctor_get_uint8(v___x_4765_, 12);
v_beta_4778_ = lean_ctor_get_uint8(v___x_4765_, 13);
v_proj_4779_ = lean_ctor_get_uint8(v___x_4765_, 14);
v_zeta_4780_ = lean_ctor_get_uint8(v___x_4765_, 15);
v_zetaDelta_4781_ = lean_ctor_get_uint8(v___x_4765_, 16);
v_zetaUnused_4782_ = lean_ctor_get_uint8(v___x_4765_, 17);
v_zetaHave_4783_ = lean_ctor_get_uint8(v___x_4765_, 18);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4765_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4785_ = v___x_4765_;
v_isShared_4786_ = v_isSharedCheck_4820_;
goto v_resetjp_4784_;
}
else
{
lean_dec(v___x_4765_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4820_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
uint8_t v_trackZetaDelta_4787_; lean_object* v_zetaDeltaSet_4788_; lean_object* v_lctx_4789_; lean_object* v_localInstances_4790_; lean_object* v_defEqCtx_x3f_4791_; lean_object* v_synthPendingDepth_4792_; lean_object* v_canUnfold_x3f_4793_; uint8_t v_univApprox_4794_; uint8_t v_inTypeClassResolution_4795_; uint8_t v_cacheInferType_4796_; uint8_t v___x_4797_; lean_object* v_config_4799_; 
v_trackZetaDelta_4787_ = lean_ctor_get_uint8(v_a_4751_, sizeof(void*)*7);
v_zetaDeltaSet_4788_ = lean_ctor_get(v_a_4751_, 1);
v_lctx_4789_ = lean_ctor_get(v_a_4751_, 2);
v_localInstances_4790_ = lean_ctor_get(v_a_4751_, 3);
v_defEqCtx_x3f_4791_ = lean_ctor_get(v_a_4751_, 4);
v_synthPendingDepth_4792_ = lean_ctor_get(v_a_4751_, 5);
v_canUnfold_x3f_4793_ = lean_ctor_get(v_a_4751_, 6);
v_univApprox_4794_ = lean_ctor_get_uint8(v_a_4751_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4795_ = lean_ctor_get_uint8(v_a_4751_, sizeof(void*)*7 + 2);
v_cacheInferType_4796_ = lean_ctor_get_uint8(v_a_4751_, sizeof(void*)*7 + 3);
v___x_4797_ = 1;
if (v_isShared_4786_ == 0)
{
v_config_4799_ = v___x_4785_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 0, v_foApprox_4766_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 1, v_ctxApprox_4767_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 2, v_quasiPatternApprox_4768_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 3, v_constApprox_4769_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 4, v_isDefEqStuckEx_4770_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 5, v_unificationHints_4771_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 6, v_proofIrrelevance_4772_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 7, v_assignSyntheticOpaque_4773_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 8, v_offsetCnstrs_4774_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 10, v_etaStruct_4775_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 11, v_univApprox_4776_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 12, v_iota_4777_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 13, v_beta_4778_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 14, v_proj_4779_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 15, v_zeta_4780_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 16, v_zetaDelta_4781_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 17, v_zetaUnused_4782_);
lean_ctor_set_uint8(v_reuseFailAlloc_4819_, 18, v_zetaHave_4783_);
v_config_4799_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
uint64_t v___x_4800_; uint64_t v___x_4801_; uint64_t v___x_4802_; lean_object* v___f_4803_; lean_object* v___f_4804_; uint64_t v___x_4805_; uint64_t v___x_4806_; uint64_t v_key_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
lean_ctor_set_uint8(v_config_4799_, 9, v___x_4797_);
v___x_4800_ = l_Lean_Meta_Context_configKey(v_a_4751_);
v___x_4801_ = 3ULL;
v___x_4802_ = lean_uint64_shift_right(v___x_4800_, v___x_4801_);
v___f_4803_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__1));
v___f_4804_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___lam__2___boxed), 16, 3);
lean_closure_set(v___f_4804_, 0, v_info_4743_);
lean_closure_set(v___f_4804_, 1, v_frameStx_4757_);
lean_closure_set(v___f_4804_, 2, v___f_4803_);
v___x_4805_ = lean_uint64_shift_left(v___x_4802_, v___x_4801_);
v___x_4806_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___closed__2);
v_key_4807_ = lean_uint64_lor(v___x_4805_, v___x_4806_);
v___x_4808_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4808_, 0, v_config_4799_);
lean_ctor_set_uint64(v___x_4808_, sizeof(void*)*1, v_key_4807_);
lean_inc(v_canUnfold_x3f_4793_);
lean_inc(v_synthPendingDepth_4792_);
lean_inc(v_defEqCtx_x3f_4791_);
lean_inc_ref(v_localInstances_4790_);
lean_inc_ref(v_lctx_4789_);
lean_inc(v_zetaDeltaSet_4788_);
v___x_4809_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
lean_ctor_set(v___x_4809_, 1, v_zetaDeltaSet_4788_);
lean_ctor_set(v___x_4809_, 2, v_lctx_4789_);
lean_ctor_set(v___x_4809_, 3, v_localInstances_4790_);
lean_ctor_set(v___x_4809_, 4, v_defEqCtx_x3f_4791_);
lean_ctor_set(v___x_4809_, 5, v_synthPendingDepth_4792_);
lean_ctor_set(v___x_4809_, 6, v_canUnfold_x3f_4793_);
lean_ctor_set_uint8(v___x_4809_, sizeof(void*)*7, v_trackZetaDelta_4787_);
lean_ctor_set_uint8(v___x_4809_, sizeof(void*)*7 + 1, v_univApprox_4794_);
lean_ctor_set_uint8(v___x_4809_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4795_);
lean_ctor_set_uint8(v___x_4809_, sizeof(void*)*7 + 3, v_cacheInferType_4796_);
v___x_4810_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_withLetDeclsDND_loop(v_a_4764_, v___f_4804_, v_decls_4759_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_, v___x_4809_, v_a_4752_, v_a_4753_, v_a_4754_);
lean_dec_ref_known(v___x_4809_, 7);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
else
{
return v___x_4810_;
}
}
}
}
else
{
lean_object* v_a_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4828_; 
lean_dec(v_frameStx_4757_);
lean_dec_ref(v_info_4743_);
v_a_4821_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4828_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4828_ == 0)
{
v___x_4823_ = v___x_4763_;
v_isShared_4824_ = v_isSharedCheck_4828_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_a_4821_);
lean_dec(v___x_4763_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame___boxed(lean_object* v_entry_4829_, lean_object* v_res_4830_, lean_object* v_info_4831_, lean_object* v_a_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_entry_4829_, v_res_4830_, v_info_4831_, v_a_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_, v_a_4839_, v_a_4840_, v_a_4841_, v_a_4842_);
lean_dec(v_a_4842_);
lean_dec_ref(v_a_4841_);
lean_dec(v_a_4840_);
lean_dec_ref(v_a_4839_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec(v_a_4833_);
lean_dec_ref(v_a_4832_);
lean_dec_ref(v_res_4830_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1(lean_object* v___x_4845_, lean_object* v_res_4846_, lean_object* v_range_4847_, lean_object* v_b_4848_, lean_object* v_i_4849_, lean_object* v_hs_4850_, lean_object* v_hl_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v___x_4864_; 
v___x_4864_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___redArg(v___x_4845_, v_res_4846_, v_range_4847_, v_b_4848_, v_i_4849_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
return v___x_4864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1___boxed(lean_object** _args){
lean_object* v___x_4865_ = _args[0];
lean_object* v_res_4866_ = _args[1];
lean_object* v_range_4867_ = _args[2];
lean_object* v_b_4868_ = _args[3];
lean_object* v_i_4869_ = _args[4];
lean_object* v_hs_4870_ = _args[5];
lean_object* v_hl_4871_ = _args[6];
lean_object* v___y_4872_ = _args[7];
lean_object* v___y_4873_ = _args[8];
lean_object* v___y_4874_ = _args[9];
lean_object* v___y_4875_ = _args[10];
lean_object* v___y_4876_ = _args[11];
lean_object* v___y_4877_ = _args[12];
lean_object* v___y_4878_ = _args[13];
lean_object* v___y_4879_ = _args[14];
lean_object* v___y_4880_ = _args[15];
lean_object* v___y_4881_ = _args[16];
lean_object* v___y_4882_ = _args[17];
lean_object* v___y_4883_ = _args[18];
_start:
{
lean_object* v_res_4884_; 
v_res_4884_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame_spec__1(v___x_4865_, v_res_4866_, v_range_4867_, v_b_4868_, v_i_4869_, v_hs_4870_, v_hl_4871_, v___y_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_);
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
lean_dec_ref(v_range_4867_);
lean_dec_ref(v_res_4866_);
lean_dec_ref(v___x_4865_);
return v_res_4884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0(lean_object* v_d_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v___x_4898_; lean_object* v_specBackwardRuleCache_4899_; lean_object* v_splitBackwardRuleCache_4900_; lean_object* v_latticeBackwardRuleCache_4901_; lean_object* v_invariants_4902_; lean_object* v_vcs_4903_; lean_object* v_simpState_4904_; lean_object* v_fuel_4905_; lean_object* v_inlineHandledInvariants_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4917_; 
v___x_4898_ = lean_st_ref_take(v___y_4887_);
v_specBackwardRuleCache_4899_ = lean_ctor_get(v___x_4898_, 0);
v_splitBackwardRuleCache_4900_ = lean_ctor_get(v___x_4898_, 1);
v_latticeBackwardRuleCache_4901_ = lean_ctor_get(v___x_4898_, 2);
v_invariants_4902_ = lean_ctor_get(v___x_4898_, 4);
v_vcs_4903_ = lean_ctor_get(v___x_4898_, 5);
v_simpState_4904_ = lean_ctor_get(v___x_4898_, 6);
v_fuel_4905_ = lean_ctor_get(v___x_4898_, 7);
v_inlineHandledInvariants_4906_ = lean_ctor_get(v___x_4898_, 8);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4898_);
if (v_isSharedCheck_4917_ == 0)
{
lean_object* v_unused_4918_; 
v_unused_4918_ = lean_ctor_get(v___x_4898_, 3);
lean_dec(v_unused_4918_);
v___x_4908_ = v___x_4898_;
v_isShared_4909_ = v_isSharedCheck_4917_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_inlineHandledInvariants_4906_);
lean_inc(v_fuel_4905_);
lean_inc(v_simpState_4904_);
lean_inc(v_vcs_4903_);
lean_inc(v_invariants_4902_);
lean_inc(v_latticeBackwardRuleCache_4901_);
lean_inc(v_splitBackwardRuleCache_4900_);
lean_inc(v_specBackwardRuleCache_4899_);
lean_dec(v___x_4898_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4917_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; lean_object* v___x_4912_; 
v___x_4910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4910_, 0, v_d_4885_);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 3, v___x_4910_);
v___x_4912_ = v___x_4908_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_specBackwardRuleCache_4899_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v_splitBackwardRuleCache_4900_);
lean_ctor_set(v_reuseFailAlloc_4916_, 2, v_latticeBackwardRuleCache_4901_);
lean_ctor_set(v_reuseFailAlloc_4916_, 3, v___x_4910_);
lean_ctor_set(v_reuseFailAlloc_4916_, 4, v_invariants_4902_);
lean_ctor_set(v_reuseFailAlloc_4916_, 5, v_vcs_4903_);
lean_ctor_set(v_reuseFailAlloc_4916_, 6, v_simpState_4904_);
lean_ctor_set(v_reuseFailAlloc_4916_, 7, v_fuel_4905_);
lean_ctor_set(v_reuseFailAlloc_4916_, 8, v_inlineHandledInvariants_4906_);
v___x_4912_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4913_ = lean_st_ref_set(v___y_4887_, v___x_4912_);
v___x_4914_ = lean_box(0);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
return v___x_4915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0___boxed(lean_object* v_d_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v_res_4932_; 
v_res_4932_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___lam__0(v_d_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_);
lean_dec(v___y_4930_);
lean_dec_ref(v___y_4929_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec(v___y_4922_);
lean_dec(v___y_4921_);
lean_dec_ref(v___y_4920_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(lean_object* v_a_4933_, lean_object* v___x_4934_, lean_object* v_as_4935_, size_t v_sz_4936_, size_t v_i_4937_, lean_object* v_b_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
lean_object* v_a_4947_; uint8_t v___x_4951_; 
v___x_4951_ = lean_usize_dec_lt(v_i_4937_, v_sz_4936_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; 
lean_dec_ref(v___x_4934_);
v___x_4952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4952_, 0, v_b_4938_);
return v___x_4952_;
}
else
{
lean_object* v_entries_4953_; lean_object* v___x_4954_; lean_object* v_a_4955_; lean_object* v___x_4956_; uint8_t v_retired_4957_; 
v_entries_4953_ = lean_ctor_get(v_a_4933_, 1);
v___x_4954_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
v_a_4955_ = lean_array_uget_borrowed(v_as_4935_, v_i_4937_);
v___x_4956_ = lean_array_get_borrowed(v___x_4954_, v_entries_4953_, v_a_4955_);
v_retired_4957_ = lean_ctor_get_uint8(v___x_4956_, sizeof(void*)*4);
if (v_retired_4957_ == 0)
{
lean_object* v_pat_4958_; lean_object* v_srcIdx_4959_; lean_object* v___x_4960_; 
v_pat_4958_ = lean_ctor_get(v___x_4956_, 0);
v_srcIdx_4959_ = lean_ctor_get(v___x_4956_, 3);
lean_inc_ref(v___x_4934_);
lean_inc_ref(v_pat_4958_);
v___x_4960_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_pat_4958_, v___x_4934_, v___x_4951_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
if (lean_obj_tag(v_a_4961_) == 1)
{
if (lean_obj_tag(v_b_4938_) == 0)
{
lean_object* v_val_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4970_; 
v_val_4962_ = lean_ctor_get(v_a_4961_, 0);
v_isSharedCheck_4970_ = !lean_is_exclusive(v_a_4961_);
if (v_isSharedCheck_4970_ == 0)
{
v___x_4964_ = v_a_4961_;
v_isShared_4965_ = v_isSharedCheck_4970_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_val_4962_);
lean_dec(v_a_4961_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4970_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4966_; lean_object* v___x_4968_; 
lean_inc(v___x_4956_);
v___x_4966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4966_, 0, v___x_4956_);
lean_ctor_set(v___x_4966_, 1, v_val_4962_);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 0, v___x_4966_);
v___x_4968_ = v___x_4964_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4969_; 
v_reuseFailAlloc_4969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4969_, 0, v___x_4966_);
v___x_4968_ = v_reuseFailAlloc_4969_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
v_a_4947_ = v___x_4968_;
goto v___jp_4946_;
}
}
}
else
{
lean_object* v_val_4971_; lean_object* v_fst_4972_; lean_object* v___x_4974_; uint8_t v_isShared_4975_; uint8_t v_isSharedCheck_4990_; 
v_val_4971_ = lean_ctor_get(v_b_4938_, 0);
lean_inc(v_val_4971_);
v_fst_4972_ = lean_ctor_get(v_val_4971_, 0);
v_isSharedCheck_4990_ = !lean_is_exclusive(v_val_4971_);
if (v_isSharedCheck_4990_ == 0)
{
lean_object* v_unused_4991_; 
v_unused_4991_ = lean_ctor_get(v_val_4971_, 1);
lean_dec(v_unused_4991_);
v___x_4974_ = v_val_4971_;
v_isShared_4975_ = v_isSharedCheck_4990_;
goto v_resetjp_4973_;
}
else
{
lean_inc(v_fst_4972_);
lean_dec(v_val_4971_);
v___x_4974_ = lean_box(0);
v_isShared_4975_ = v_isSharedCheck_4990_;
goto v_resetjp_4973_;
}
v_resetjp_4973_:
{
lean_object* v_val_4976_; lean_object* v_srcIdx_4977_; uint8_t v___x_4978_; 
v_val_4976_ = lean_ctor_get(v_a_4961_, 0);
lean_inc(v_val_4976_);
lean_dec_ref_known(v_a_4961_, 1);
v_srcIdx_4977_ = lean_ctor_get(v_fst_4972_, 3);
lean_inc(v_srcIdx_4977_);
lean_dec(v_fst_4972_);
v___x_4978_ = lean_nat_dec_lt(v_srcIdx_4959_, v_srcIdx_4977_);
lean_dec(v_srcIdx_4977_);
if (v___x_4978_ == 0)
{
lean_dec(v_val_4976_);
lean_del_object(v___x_4974_);
v_a_4947_ = v_b_4938_;
goto v___jp_4946_;
}
else
{
lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4988_; 
v_isSharedCheck_4988_ = !lean_is_exclusive(v_b_4938_);
if (v_isSharedCheck_4988_ == 0)
{
lean_object* v_unused_4989_; 
v_unused_4989_ = lean_ctor_get(v_b_4938_, 0);
lean_dec(v_unused_4989_);
v___x_4980_ = v_b_4938_;
v_isShared_4981_ = v_isSharedCheck_4988_;
goto v_resetjp_4979_;
}
else
{
lean_dec(v_b_4938_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4988_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4983_; 
lean_inc(v___x_4956_);
if (v_isShared_4975_ == 0)
{
lean_ctor_set(v___x_4974_, 1, v_val_4976_);
lean_ctor_set(v___x_4974_, 0, v___x_4956_);
v___x_4983_ = v___x_4974_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v___x_4956_);
lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_val_4976_);
v___x_4983_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
lean_object* v___x_4985_; 
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 0, v___x_4983_);
v___x_4985_ = v___x_4980_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v___x_4983_);
v___x_4985_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
v_a_4947_ = v___x_4985_;
goto v___jp_4946_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_4961_);
v_a_4947_ = v_b_4938_;
goto v___jp_4946_;
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_4999_; 
lean_dec(v_b_4938_);
lean_dec_ref(v___x_4934_);
v_a_4992_ = lean_ctor_get(v___x_4960_, 0);
v_isSharedCheck_4999_ = !lean_is_exclusive(v___x_4960_);
if (v_isSharedCheck_4999_ == 0)
{
v___x_4994_ = v___x_4960_;
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v___x_4960_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_4999_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v___x_4997_; 
if (v_isShared_4995_ == 0)
{
v___x_4997_ = v___x_4994_;
goto v_reusejp_4996_;
}
else
{
lean_object* v_reuseFailAlloc_4998_; 
v_reuseFailAlloc_4998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4998_, 0, v_a_4992_);
v___x_4997_ = v_reuseFailAlloc_4998_;
goto v_reusejp_4996_;
}
v_reusejp_4996_:
{
return v___x_4997_;
}
}
}
}
else
{
v_a_4947_ = v_b_4938_;
goto v___jp_4946_;
}
}
v___jp_4946_:
{
size_t v___x_4948_; size_t v___x_4949_; 
v___x_4948_ = ((size_t)1ULL);
v___x_4949_ = lean_usize_add(v_i_4937_, v___x_4948_);
v_i_4937_ = v___x_4949_;
v_b_4938_ = v_a_4947_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg___boxed(lean_object* v_a_5000_, lean_object* v___x_5001_, lean_object* v_as_5002_, lean_object* v_sz_5003_, lean_object* v_i_5004_, lean_object* v_b_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_, lean_object* v___y_5012_){
_start:
{
size_t v_sz_boxed_5013_; size_t v_i_boxed_5014_; lean_object* v_res_5015_; 
v_sz_boxed_5013_ = lean_unbox_usize(v_sz_5003_);
lean_dec(v_sz_5003_);
v_i_boxed_5014_ = lean_unbox_usize(v_i_5004_);
lean_dec(v_i_5004_);
v_res_5015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_a_5000_, v___x_5001_, v_as_5002_, v_sz_boxed_5013_, v_i_boxed_5014_, v_b_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
lean_dec(v___y_5011_);
lean_dec_ref(v___y_5010_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
lean_dec_ref(v_as_5002_);
lean_dec_ref(v_a_5000_);
return v_res_5015_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2(void){
_start:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__1));
v___x_5019_ = l_Lean_stringToMessageData(v___x_5018_);
return v___x_5019_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__3));
v___x_5022_ = l_Lean_stringToMessageData(v___x_5021_);
return v___x_5022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(lean_object* v_info_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_, lean_object* v_a_5026_, lean_object* v_a_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_, lean_object* v_a_5034_){
_start:
{
lean_object* v___y_5037_; lean_object* v___x_5040_; lean_object* v_frameDB_x3f_5041_; 
v___x_5040_ = lean_st_ref_get(v_a_5025_);
v_frameDB_x3f_5041_ = lean_ctor_get(v___x_5040_, 3);
lean_inc(v_frameDB_x3f_5041_);
lean_dec(v___x_5040_);
if (lean_obj_tag(v_frameDB_x3f_5041_) == 1)
{
lean_object* v_val_5042_; lean_object* v___f_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; 
v_val_5042_ = lean_ctor_get(v_frameDB_x3f_5041_, 0);
lean_inc(v_val_5042_);
lean_dec_ref_known(v_frameDB_x3f_5041_, 1);
v___f_5043_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__0));
v___x_5044_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_5023_);
v___x_5045_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern_spec__0___redArg(v_val_5042_, v___f_5043_, v___x_5044_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
if (lean_obj_tag(v___x_5045_) == 0)
{
lean_object* v_a_5046_; lean_object* v_tree_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; size_t v_sz_5051_; size_t v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5171_; 
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc(v_a_5046_);
lean_dec_ref_known(v___x_5045_, 1);
v_tree_5047_ = lean_ctor_get(v_a_5046_, 0);
v___x_5048_ = lean_box(0);
v___x_5049_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_5023_);
v___x_5050_ = l_Lean_Meta_Sym_getMatch___redArg(v_tree_5047_, v___x_5049_);
v_sz_5051_ = lean_array_size(v___x_5050_);
v___x_5052_ = ((size_t)0ULL);
lean_inc_ref(v___x_5049_);
v___x_5053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_a_5046_, v___x_5049_, v___x_5050_, v_sz_5051_, v___x_5052_, v___x_5048_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
lean_dec_ref(v___x_5050_);
v_isSharedCheck_5171_ = !lean_is_exclusive(v_a_5046_);
if (v_isSharedCheck_5171_ == 0)
{
lean_object* v_unused_5172_; lean_object* v_unused_5173_; 
v_unused_5172_ = lean_ctor_get(v_a_5046_, 1);
lean_dec(v_unused_5172_);
v_unused_5173_ = lean_ctor_get(v_a_5046_, 0);
lean_dec(v_unused_5173_);
v___x_5055_ = v_a_5046_;
v_isShared_5056_ = v_isSharedCheck_5171_;
goto v_resetjp_5054_;
}
else
{
lean_dec(v_a_5046_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5171_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
if (lean_obj_tag(v___x_5053_) == 0)
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5162_; 
v_a_5057_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5162_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5162_ == 0)
{
v___x_5059_ = v___x_5053_;
v_isShared_5060_ = v_isSharedCheck_5162_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___x_5053_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5162_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
if (lean_obj_tag(v_a_5057_) == 1)
{
lean_object* v_val_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5158_; 
lean_del_object(v___x_5059_);
v_val_5061_ = lean_ctor_get(v_a_5057_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v_a_5057_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5063_ = v_a_5057_;
v_isShared_5064_ = v_isSharedCheck_5158_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_val_5061_);
lean_dec(v_a_5057_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5158_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v_fst_5065_; lean_object* v_snd_5066_; lean_object* v___x_5068_; uint8_t v_isShared_5069_; uint8_t v_isSharedCheck_5157_; 
v_fst_5065_ = lean_ctor_get(v_val_5061_, 0);
v_snd_5066_ = lean_ctor_get(v_val_5061_, 1);
v_isSharedCheck_5157_ = !lean_is_exclusive(v_val_5061_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5068_ = v_val_5061_;
v_isShared_5069_ = v_isSharedCheck_5157_;
goto v_resetjp_5067_;
}
else
{
lean_inc(v_snd_5066_);
lean_inc(v_fst_5065_);
lean_dec(v_val_5061_);
v___x_5068_ = lean_box(0);
v_isShared_5069_ = v_isSharedCheck_5157_;
goto v_resetjp_5067_;
}
v_resetjp_5067_:
{
lean_object* v___x_5070_; lean_object* v_specBackwardRuleCache_5071_; lean_object* v_splitBackwardRuleCache_5072_; lean_object* v_latticeBackwardRuleCache_5073_; lean_object* v_frameDB_x3f_5074_; lean_object* v_invariants_5075_; lean_object* v_vcs_5076_; lean_object* v_simpState_5077_; lean_object* v_fuel_5078_; lean_object* v_inlineHandledInvariants_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5156_; 
v___x_5070_ = lean_st_ref_take(v_a_5025_);
v_specBackwardRuleCache_5071_ = lean_ctor_get(v___x_5070_, 0);
v_splitBackwardRuleCache_5072_ = lean_ctor_get(v___x_5070_, 1);
v_latticeBackwardRuleCache_5073_ = lean_ctor_get(v___x_5070_, 2);
v_frameDB_x3f_5074_ = lean_ctor_get(v___x_5070_, 3);
v_invariants_5075_ = lean_ctor_get(v___x_5070_, 4);
v_vcs_5076_ = lean_ctor_get(v___x_5070_, 5);
v_simpState_5077_ = lean_ctor_get(v___x_5070_, 6);
v_fuel_5078_ = lean_ctor_get(v___x_5070_, 7);
v_inlineHandledInvariants_5079_ = lean_ctor_get(v___x_5070_, 8);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5156_ == 0)
{
v___x_5081_ = v___x_5070_;
v_isShared_5082_ = v_isSharedCheck_5156_;
goto v_resetjp_5080_;
}
else
{
lean_inc(v_inlineHandledInvariants_5079_);
lean_inc(v_fuel_5078_);
lean_inc(v_simpState_5077_);
lean_inc(v_vcs_5076_);
lean_inc(v_invariants_5075_);
lean_inc(v_frameDB_x3f_5074_);
lean_inc(v_latticeBackwardRuleCache_5073_);
lean_inc(v_splitBackwardRuleCache_5072_);
lean_inc(v_specBackwardRuleCache_5071_);
lean_dec(v___x_5070_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5156_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___y_5084_; lean_object* v___y_5127_; 
if (lean_obj_tag(v_frameDB_x3f_5074_) == 0)
{
lean_del_object(v___x_5063_);
v___y_5084_ = v_frameDB_x3f_5074_;
goto v___jp_5083_;
}
else
{
lean_object* v_val_5131_; 
v_val_5131_ = lean_ctor_get(v_frameDB_x3f_5074_, 0);
lean_inc(v_val_5131_);
lean_dec_ref_known(v_frameDB_x3f_5074_, 1);
if (lean_obj_tag(v_val_5131_) == 1)
{
lean_object* v_value_5132_; lean_object* v___x_5134_; uint8_t v_isShared_5135_; uint8_t v_isSharedCheck_5155_; 
v_value_5132_ = lean_ctor_get(v_val_5131_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v_val_5131_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5134_ = v_val_5131_;
v_isShared_5135_ = v_isSharedCheck_5155_;
goto v_resetjp_5133_;
}
else
{
lean_inc(v_value_5132_);
lean_dec(v_val_5131_);
v___x_5134_ = lean_box(0);
v_isShared_5135_ = v_isSharedCheck_5155_;
goto v_resetjp_5133_;
}
v_resetjp_5133_:
{
lean_object* v_tree_5136_; lean_object* v_entries_5137_; lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5154_; 
v_tree_5136_ = lean_ctor_get(v_value_5132_, 0);
v_entries_5137_ = lean_ctor_get(v_value_5132_, 1);
v_isSharedCheck_5154_ = !lean_is_exclusive(v_value_5132_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5139_ = v_value_5132_;
v_isShared_5140_ = v_isSharedCheck_5154_;
goto v_resetjp_5138_;
}
else
{
lean_inc(v_entries_5137_);
lean_inc(v_tree_5136_);
lean_dec(v_value_5132_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5154_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v_pat_5141_; lean_object* v_varNames_5142_; lean_object* v_frameStx_5143_; lean_object* v_srcIdx_5144_; uint8_t v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5149_; 
v_pat_5141_ = lean_ctor_get(v_fst_5065_, 0);
v_varNames_5142_ = lean_ctor_get(v_fst_5065_, 1);
v_frameStx_5143_ = lean_ctor_get(v_fst_5065_, 2);
v_srcIdx_5144_ = lean_ctor_get(v_fst_5065_, 3);
v___x_5145_ = 1;
lean_inc(v_srcIdx_5144_);
lean_inc(v_frameStx_5143_);
lean_inc_ref(v_varNames_5142_);
lean_inc_ref(v_pat_5141_);
v___x_5146_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_5146_, 0, v_pat_5141_);
lean_ctor_set(v___x_5146_, 1, v_varNames_5142_);
lean_ctor_set(v___x_5146_, 2, v_frameStx_5143_);
lean_ctor_set(v___x_5146_, 3, v_srcIdx_5144_);
lean_ctor_set_uint8(v___x_5146_, sizeof(void*)*4, v___x_5145_);
v___x_5147_ = lean_array_set(v_entries_5137_, v_srcIdx_5144_, v___x_5146_);
if (v_isShared_5140_ == 0)
{
lean_ctor_set(v___x_5139_, 1, v___x_5147_);
v___x_5149_ = v___x_5139_;
goto v_reusejp_5148_;
}
else
{
lean_object* v_reuseFailAlloc_5153_; 
v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5153_, 0, v_tree_5136_);
lean_ctor_set(v_reuseFailAlloc_5153_, 1, v___x_5147_);
v___x_5149_ = v_reuseFailAlloc_5153_;
goto v_reusejp_5148_;
}
v_reusejp_5148_:
{
lean_object* v___x_5151_; 
if (v_isShared_5135_ == 0)
{
lean_ctor_set(v___x_5134_, 0, v___x_5149_);
v___x_5151_ = v___x_5134_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
v___y_5127_ = v___x_5151_;
goto v___jp_5126_;
}
}
}
}
}
else
{
v___y_5127_ = v_val_5131_;
goto v___jp_5126_;
}
}
v___jp_5083_:
{
lean_object* v___x_5086_; 
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 3, v___y_5084_);
v___x_5086_ = v___x_5081_;
goto v_reusejp_5085_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_specBackwardRuleCache_5071_);
lean_ctor_set(v_reuseFailAlloc_5125_, 1, v_splitBackwardRuleCache_5072_);
lean_ctor_set(v_reuseFailAlloc_5125_, 2, v_latticeBackwardRuleCache_5073_);
lean_ctor_set(v_reuseFailAlloc_5125_, 3, v___y_5084_);
lean_ctor_set(v_reuseFailAlloc_5125_, 4, v_invariants_5075_);
lean_ctor_set(v_reuseFailAlloc_5125_, 5, v_vcs_5076_);
lean_ctor_set(v_reuseFailAlloc_5125_, 6, v_simpState_5077_);
lean_ctor_set(v_reuseFailAlloc_5125_, 7, v_fuel_5078_);
lean_ctor_set(v_reuseFailAlloc_5125_, 8, v_inlineHandledInvariants_5079_);
v___x_5086_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5085_;
}
v_reusejp_5085_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; 
v___x_5087_ = lean_st_ref_set(v_a_5025_, v___x_5086_);
v___x_5088_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_elabFrame(v_fst_5065_, v_snd_5066_, v_info_5023_, v_a_5024_, v_a_5025_, v_a_5026_, v_a_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
lean_dec(v_snd_5066_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_options_5089_; uint8_t v_hasTrace_5090_; 
v_options_5089_ = lean_ctor_get(v_a_5033_, 2);
v_hasTrace_5090_ = lean_ctor_get_uint8(v_options_5089_, sizeof(void*)*1);
if (v_hasTrace_5090_ == 0)
{
lean_object* v_a_5091_; 
lean_del_object(v___x_5068_);
lean_del_object(v___x_5055_);
lean_dec_ref(v___x_5049_);
v_a_5091_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5091_);
lean_dec_ref_known(v___x_5088_, 1);
v___y_5037_ = v_a_5091_;
goto v___jp_5036_;
}
else
{
lean_object* v_a_5092_; lean_object* v_inheritedTraceOptions_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; uint8_t v___x_5096_; 
v_a_5092_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5092_);
lean_dec_ref_known(v___x_5088_, 1);
v_inheritedTraceOptions_5093_ = lean_ctor_get(v_a_5033_, 13);
v___x_5094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_5095_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5093_, v_options_5089_, v___x_5095_);
if (v___x_5096_ == 0)
{
lean_del_object(v___x_5068_);
lean_del_object(v___x_5055_);
lean_dec_ref(v___x_5049_);
v___y_5037_ = v_a_5092_;
goto v___jp_5036_;
}
else
{
lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5100_; 
v___x_5097_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__2);
v___x_5098_ = l_Lean_MessageData_ofExpr(v___x_5049_);
if (v_isShared_5069_ == 0)
{
lean_ctor_set_tag(v___x_5068_, 7);
lean_ctor_set(v___x_5068_, 1, v___x_5098_);
lean_ctor_set(v___x_5068_, 0, v___x_5097_);
v___x_5100_ = v___x_5068_;
goto v_reusejp_5099_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v___x_5097_);
lean_ctor_set(v_reuseFailAlloc_5116_, 1, v___x_5098_);
v___x_5100_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5099_;
}
v_reusejp_5099_:
{
lean_object* v___x_5101_; lean_object* v___x_5103_; 
v___x_5101_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___closed__4);
if (v_isShared_5056_ == 0)
{
lean_ctor_set_tag(v___x_5055_, 7);
lean_ctor_set(v___x_5055_, 1, v___x_5101_);
lean_ctor_set(v___x_5055_, 0, v___x_5100_);
v___x_5103_ = v___x_5055_;
goto v_reusejp_5102_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v___x_5100_);
lean_ctor_set(v_reuseFailAlloc_5115_, 1, v___x_5101_);
v___x_5103_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5102_;
}
v_reusejp_5102_:
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; 
lean_inc(v_a_5092_);
v___x_5104_ = l_Lean_indentExpr(v_a_5092_);
v___x_5105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5105_, 0, v___x_5103_);
lean_ctor_set(v___x_5105_, 1, v___x_5104_);
v___x_5106_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5094_, v___x_5105_, v_a_5031_, v_a_5032_, v_a_5033_, v_a_5034_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_dec_ref_known(v___x_5106_, 1);
v___y_5037_ = v_a_5092_;
goto v___jp_5036_;
}
else
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
lean_dec(v_a_5092_);
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5106_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5106_);
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
}
}
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_del_object(v___x_5068_);
lean_del_object(v___x_5055_);
lean_dec_ref(v___x_5049_);
v_a_5117_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___x_5088_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___x_5088_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
if (v_isShared_5120_ == 0)
{
v___x_5122_ = v___x_5119_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
}
v___jp_5126_:
{
lean_object* v___x_5129_; 
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 0, v___y_5127_);
v___x_5129_ = v___x_5063_;
goto v_reusejp_5128_;
}
else
{
lean_object* v_reuseFailAlloc_5130_; 
v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5130_, 0, v___y_5127_);
v___x_5129_ = v_reuseFailAlloc_5130_;
goto v_reusejp_5128_;
}
v_reusejp_5128_:
{
v___y_5084_ = v___x_5129_;
goto v___jp_5083_;
}
}
}
}
}
}
else
{
lean_object* v___x_5160_; 
lean_dec(v_a_5057_);
lean_del_object(v___x_5055_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v_info_5023_);
if (v_isShared_5060_ == 0)
{
lean_ctor_set(v___x_5059_, 0, v___x_5048_);
v___x_5160_ = v___x_5059_;
goto v_reusejp_5159_;
}
else
{
lean_object* v_reuseFailAlloc_5161_; 
v_reuseFailAlloc_5161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5161_, 0, v___x_5048_);
v___x_5160_ = v_reuseFailAlloc_5161_;
goto v_reusejp_5159_;
}
v_reusejp_5159_:
{
return v___x_5160_;
}
}
}
}
else
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
lean_del_object(v___x_5055_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v_info_5023_);
v_a_5163_ = lean_ctor_get(v___x_5053_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5053_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5053_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5053_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
return v___x_5168_;
}
}
}
}
}
else
{
lean_object* v_a_5174_; lean_object* v___x_5176_; uint8_t v_isShared_5177_; uint8_t v_isSharedCheck_5181_; 
lean_dec_ref(v_info_5023_);
v_a_5174_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5176_ = v___x_5045_;
v_isShared_5177_ = v_isSharedCheck_5181_;
goto v_resetjp_5175_;
}
else
{
lean_inc(v_a_5174_);
lean_dec(v___x_5045_);
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
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; 
lean_dec(v_frameDB_x3f_5041_);
lean_dec_ref(v_info_5023_);
v___x_5182_ = lean_box(0);
v___x_5183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
return v___x_5183_;
}
v___jp_5036_:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5038_, 0, v___y_5037_);
v___x_5039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5039_, 0, v___x_5038_);
return v___x_5039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f___boxed(lean_object* v_info_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_, lean_object* v_a_5191_, lean_object* v_a_5192_, lean_object* v_a_5193_, lean_object* v_a_5194_, lean_object* v_a_5195_, lean_object* v_a_5196_){
_start:
{
lean_object* v_res_5197_; 
v_res_5197_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_info_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_, v_a_5191_, v_a_5192_, v_a_5193_, v_a_5194_, v_a_5195_);
lean_dec(v_a_5195_);
lean_dec_ref(v_a_5194_);
lean_dec(v_a_5193_);
lean_dec_ref(v_a_5192_);
lean_dec(v_a_5191_);
lean_dec_ref(v_a_5190_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
lean_dec(v_a_5187_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
return v_res_5197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(lean_object* v_a_5198_, lean_object* v___x_5199_, lean_object* v_as_5200_, size_t v_sz_5201_, size_t v_i_5202_, lean_object* v_b_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_, lean_object* v___y_5209_, lean_object* v___y_5210_, lean_object* v___y_5211_, lean_object* v___y_5212_, lean_object* v___y_5213_, lean_object* v___y_5214_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___redArg(v_a_5198_, v___x_5199_, v_as_5200_, v_sz_5201_, v_i_5202_, v_b_5203_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0___boxed(lean_object** _args){
lean_object* v_a_5217_ = _args[0];
lean_object* v___x_5218_ = _args[1];
lean_object* v_as_5219_ = _args[2];
lean_object* v_sz_5220_ = _args[3];
lean_object* v_i_5221_ = _args[4];
lean_object* v_b_5222_ = _args[5];
lean_object* v___y_5223_ = _args[6];
lean_object* v___y_5224_ = _args[7];
lean_object* v___y_5225_ = _args[8];
lean_object* v___y_5226_ = _args[9];
lean_object* v___y_5227_ = _args[10];
lean_object* v___y_5228_ = _args[11];
lean_object* v___y_5229_ = _args[12];
lean_object* v___y_5230_ = _args[13];
lean_object* v___y_5231_ = _args[14];
lean_object* v___y_5232_ = _args[15];
lean_object* v___y_5233_ = _args[16];
lean_object* v___y_5234_ = _args[17];
_start:
{
size_t v_sz_boxed_5235_; size_t v_i_boxed_5236_; lean_object* v_res_5237_; 
v_sz_boxed_5235_ = lean_unbox_usize(v_sz_5220_);
lean_dec(v_sz_5220_);
v_i_boxed_5236_ = lean_unbox_usize(v_i_5221_);
lean_dec(v_i_5221_);
v_res_5237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f_spec__0(v_a_5217_, v___x_5218_, v_as_5219_, v_sz_boxed_5235_, v_i_boxed_5236_, v_b_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_);
lean_dec(v___y_5233_);
lean_dec_ref(v___y_5232_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec_ref(v_as_5219_);
lean_dec_ref(v_a_5217_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx(lean_object* v_x_5238_){
_start:
{
if (lean_obj_tag(v_x_5238_) == 0)
{
lean_object* v___x_5239_; 
v___x_5239_ = lean_unsigned_to_nat(0u);
return v___x_5239_;
}
else
{
lean_object* v___x_5240_; 
v___x_5240_ = lean_unsigned_to_nat(1u);
return v___x_5240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx___boxed(lean_object* v_x_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorIdx(v_x_5241_);
lean_dec_ref(v_x_5241_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(lean_object* v_t_5243_, lean_object* v_k_5244_){
_start:
{
if (lean_obj_tag(v_t_5243_) == 0)
{
lean_object* v_scope_5245_; lean_object* v_subgoals_5246_; lean_object* v___x_5247_; 
v_scope_5245_ = lean_ctor_get(v_t_5243_, 0);
lean_inc_ref(v_scope_5245_);
v_subgoals_5246_ = lean_ctor_get(v_t_5243_, 1);
lean_inc(v_subgoals_5246_);
lean_dec_ref_known(v_t_5243_, 2);
v___x_5247_ = lean_apply_2(v_k_5244_, v_scope_5245_, v_subgoals_5246_);
return v___x_5247_;
}
else
{
lean_object* v_goal_5248_; lean_object* v_info_5249_; lean_object* v___x_5250_; 
v_goal_5248_ = lean_ctor_get(v_t_5243_, 0);
lean_inc(v_goal_5248_);
v_info_5249_ = lean_ctor_get(v_t_5243_, 1);
lean_inc_ref(v_info_5249_);
lean_dec_ref_known(v_t_5243_, 2);
v___x_5250_ = lean_apply_2(v_k_5244_, v_goal_5248_, v_info_5249_);
return v___x_5250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim(lean_object* v_motive_5251_, lean_object* v_ctorIdx_5252_, lean_object* v_t_5253_, lean_object* v_h_5254_, lean_object* v_k_5255_){
_start:
{
lean_object* v___x_5256_; 
v___x_5256_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5253_, v_k_5255_);
return v___x_5256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___boxed(lean_object* v_motive_5257_, lean_object* v_ctorIdx_5258_, lean_object* v_t_5259_, lean_object* v_h_5260_, lean_object* v_k_5261_){
_start:
{
lean_object* v_res_5262_; 
v_res_5262_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim(v_motive_5257_, v_ctorIdx_5258_, v_t_5259_, v_h_5260_, v_k_5261_);
lean_dec(v_ctorIdx_5258_);
return v_res_5262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_framed_elim___redArg(lean_object* v_t_5263_, lean_object* v_framed_5264_){
_start:
{
lean_object* v___x_5265_; 
v___x_5265_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5263_, v_framed_5264_);
return v___x_5265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_framed_elim(lean_object* v_motive_5266_, lean_object* v_t_5267_, lean_object* v_h_5268_, lean_object* v_framed_5269_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5267_, v_framed_5269_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_notFramed_elim___redArg(lean_object* v_t_5271_, lean_object* v_notFramed_5272_){
_start:
{
lean_object* v___x_5273_; 
v___x_5273_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5271_, v_notFramed_5272_);
return v___x_5273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_notFramed_elim(lean_object* v_motive_5274_, lean_object* v_t_5275_, lean_object* v_h_5276_, lean_object* v_notFramed_5277_){
_start:
{
lean_object* v___x_5278_; 
v___x_5278_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_FrameResult_ctorElim___redArg(v_t_5275_, v_notFramed_5277_);
return v___x_5278_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(size_t v_sz_5279_, size_t v_i_5280_, lean_object* v_bs_5281_){
_start:
{
uint8_t v___x_5282_; 
v___x_5282_ = lean_usize_dec_lt(v_i_5280_, v_sz_5279_);
if (v___x_5282_ == 0)
{
return v_bs_5281_;
}
else
{
lean_object* v_v_5283_; lean_object* v___x_5284_; lean_object* v_bs_x27_5285_; lean_object* v___x_5286_; size_t v___x_5287_; size_t v___x_5288_; lean_object* v___x_5289_; 
v_v_5283_ = lean_array_uget(v_bs_5281_, v_i_5280_);
v___x_5284_ = lean_unsigned_to_nat(0u);
v_bs_x27_5285_ = lean_array_uset(v_bs_5281_, v_i_5280_, v___x_5284_);
v___x_5286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5286_, 0, v_v_5283_);
v___x_5287_ = ((size_t)1ULL);
v___x_5288_ = lean_usize_add(v_i_5280_, v___x_5287_);
v___x_5289_ = lean_array_uset(v_bs_x27_5285_, v_i_5280_, v___x_5286_);
v_i_5280_ = v___x_5288_;
v_bs_5281_ = v___x_5289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0___boxed(lean_object* v_sz_5291_, lean_object* v_i_5292_, lean_object* v_bs_5293_){
_start:
{
size_t v_sz_boxed_5294_; size_t v_i_boxed_5295_; lean_object* v_res_5296_; 
v_sz_boxed_5294_ = lean_unbox_usize(v_sz_5291_);
lean_dec(v_sz_5291_);
v_i_boxed_5295_ = lean_unbox_usize(v_i_5292_);
lean_dec(v_i_5292_);
v_res_5296_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(v_sz_boxed_5294_, v_i_boxed_5295_, v_bs_5293_);
return v_res_5296_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; 
v___x_5298_ = lean_box(0);
v___x_5299_ = lean_unsigned_to_nat(2u);
v___x_5300_ = lean_mk_empty_array_with_capacity(v___x_5299_);
v___x_5301_ = lean_array_push(v___x_5300_, v___x_5298_);
return v___x_5301_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5303_; lean_object* v___x_5304_; 
v___x_5303_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__2));
v___x_5304_ = l_Lean_stringToMessageData(v___x_5303_);
return v___x_5304_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5306_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__4));
v___x_5307_ = l_Lean_stringToMessageData(v___x_5306_);
return v___x_5307_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5309_; lean_object* v___x_5310_; 
v___x_5309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__6));
v___x_5310_ = l_Lean_stringToMessageData(v___x_5309_);
return v___x_5310_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__8));
v___x_5313_ = l_Lean_stringToMessageData(v___x_5312_);
return v___x_5313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0(uint8_t v___x_5314_, lean_object* v_info_5315_, lean_object* v___x_5316_, lean_object* v___x_5317_, lean_object* v___x_5318_, lean_object* v___x_5319_, lean_object* v___x_5320_, lean_object* v_goal_5321_, lean_object* v_scope_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_){
_start:
{
if (v___x_5314_ == 0)
{
lean_object* v___x_5335_; 
lean_inc_ref(v_info_5315_);
v___x_5335_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchFrame_x3f(v_info_5315_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
if (lean_obj_tag(v___x_5335_) == 0)
{
lean_object* v_a_5336_; lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5431_; 
v_a_5336_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5338_ = v___x_5335_;
v_isShared_5339_ = v_isSharedCheck_5431_;
goto v_resetjp_5337_;
}
else
{
lean_inc(v_a_5336_);
lean_dec(v___x_5335_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5431_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
if (lean_obj_tag(v_a_5336_) == 1)
{
lean_object* v_args_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; size_t v_sz_5346_; size_t v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; 
lean_del_object(v___x_5338_);
v_args_5340_ = lean_ctor_get(v_info_5315_, 1);
v___x_5341_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__0));
v___x_5342_ = l_Lean_Name_mkStr5(v___x_5316_, v___x_5317_, v___x_5318_, v___x_5319_, v___x_5341_);
v___x_5343_ = lean_unsigned_to_nat(7u);
v___x_5344_ = lean_unsigned_to_nat(0u);
v___x_5345_ = l_Array_extract___redArg(v_args_5340_, v___x_5344_, v___x_5343_);
v_sz_5346_ = lean_array_size(v___x_5345_);
v___x_5347_ = ((size_t)0ULL);
v___x_5348_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame_spec__0(v_sz_5346_, v___x_5347_, v___x_5345_);
v___x_5349_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__1);
v___x_5350_ = lean_array_push(v___x_5349_, v_a_5336_);
v___x_5351_ = l_Array_append___redArg(v___x_5348_, v___x_5350_);
lean_dec_ref(v___x_5350_);
v___x_5352_ = l_Lean_Meta_mkAppOptM(v___x_5342_, v___x_5351_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_object* v_a_5353_; lean_object* v_ref_5354_; lean_object* v___x_5355_; lean_object* v___x_5356_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
lean_inc(v_a_5353_);
lean_dec_ref_known(v___x_5352_, 1);
v_ref_5354_ = lean_ctor_get(v___y_5332_, 5);
v___x_5355_ = lean_unsigned_to_nat(1000u);
lean_inc(v_ref_5354_);
v___x_5356_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromStx(v_ref_5354_, v_a_5353_, v___x_5355_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
if (lean_obj_tag(v___x_5356_) == 0)
{
lean_object* v_a_5357_; 
v_a_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_a_5357_);
lean_dec_ref_known(v___x_5356_, 1);
if (lean_obj_tag(v_a_5357_) == 1)
{
lean_object* v_val_5358_; lean_object* v___x_5359_; lean_object* v___x_5360_; 
v_val_5358_ = lean_ctor_get(v_a_5357_, 0);
lean_inc(v_val_5358_);
lean_dec_ref_known(v_a_5357_, 1);
v___x_5359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__2));
v___x_5360_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_tryMkBackwardRuleFromSpec(v_val_5358_, v_info_5315_, v___x_5359_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
lean_dec_ref(v_info_5315_);
if (lean_obj_tag(v___x_5360_) == 0)
{
lean_object* v_a_5361_; 
v_a_5361_ = lean_ctor_get(v___x_5360_, 0);
lean_inc(v_a_5361_);
lean_dec_ref_known(v___x_5360_, 1);
if (lean_obj_tag(v_a_5361_) == 1)
{
lean_object* v_val_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5394_; 
v_val_5362_ = lean_ctor_get(v_a_5361_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v_a_5361_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5364_ = v_a_5361_;
v_isShared_5365_ = v_isSharedCheck_5394_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_val_5362_);
lean_dec(v_a_5361_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5394_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5370_; 
v___x_5366_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__3);
v___x_5367_ = l_Lean_indentExpr(v___x_5320_);
lean_inc_ref(v___x_5367_);
v___x_5368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5368_, 0, v___x_5366_);
lean_ctor_set(v___x_5368_, 1, v___x_5367_);
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 0, v___x_5368_);
v___x_5370_ = v___x_5364_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v___x_5368_);
v___x_5370_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
lean_object* v___x_5371_; 
v___x_5371_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_5362_, v_goal_5321_, v___x_5370_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5384_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5384_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5384_ == 0)
{
v___x_5374_ = v___x_5371_;
v_isShared_5375_ = v_isSharedCheck_5384_;
goto v_resetjp_5373_;
}
else
{
lean_inc(v_a_5372_);
lean_dec(v___x_5371_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5384_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
if (lean_obj_tag(v_a_5372_) == 1)
{
lean_object* v_mvarIds_5376_; lean_object* v___x_5377_; lean_object* v___x_5379_; 
lean_dec_ref(v___x_5367_);
v_mvarIds_5376_ = lean_ctor_get(v_a_5372_, 0);
lean_inc(v_mvarIds_5376_);
lean_dec_ref_known(v_a_5372_, 1);
v___x_5377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5377_, 0, v_scope_5322_);
lean_ctor_set(v___x_5377_, 1, v_mvarIds_5376_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 0, v___x_5377_);
v___x_5379_ = v___x_5374_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5377_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
else
{
lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; 
lean_del_object(v___x_5374_);
lean_dec(v_a_5372_);
lean_dec_ref(v_scope_5322_);
v___x_5381_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__5);
v___x_5382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5382_, 0, v___x_5381_);
lean_ctor_set(v___x_5382_, 1, v___x_5367_);
v___x_5383_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5382_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
return v___x_5383_;
}
}
}
else
{
lean_object* v_a_5385_; lean_object* v___x_5387_; uint8_t v_isShared_5388_; uint8_t v_isSharedCheck_5392_; 
lean_dec_ref(v___x_5367_);
lean_dec_ref(v_scope_5322_);
v_a_5385_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5392_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5392_ == 0)
{
v___x_5387_ = v___x_5371_;
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
else
{
lean_inc(v_a_5385_);
lean_dec(v___x_5371_);
v___x_5387_ = lean_box(0);
v_isShared_5388_ = v_isSharedCheck_5392_;
goto v_resetjp_5386_;
}
v_resetjp_5386_:
{
lean_object* v___x_5390_; 
if (v_isShared_5388_ == 0)
{
v___x_5390_ = v___x_5387_;
goto v_reusejp_5389_;
}
else
{
lean_object* v_reuseFailAlloc_5391_; 
v_reuseFailAlloc_5391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
v___x_5390_ = v_reuseFailAlloc_5391_;
goto v_reusejp_5389_;
}
v_reusejp_5389_:
{
return v___x_5390_;
}
}
}
}
}
}
else
{
lean_object* v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; 
lean_dec(v_a_5361_);
lean_dec_ref(v_scope_5322_);
lean_dec(v_goal_5321_);
v___x_5395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__7);
v___x_5396_ = l_Lean_indentExpr(v___x_5320_);
v___x_5397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5397_, 0, v___x_5395_);
lean_ctor_set(v___x_5397_, 1, v___x_5396_);
v___x_5398_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5397_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
return v___x_5398_;
}
}
else
{
lean_object* v_a_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5406_; 
lean_dec_ref(v_scope_5322_);
lean_dec(v_goal_5321_);
lean_dec_ref(v___x_5320_);
v_a_5399_ = lean_ctor_get(v___x_5360_, 0);
v_isSharedCheck_5406_ = !lean_is_exclusive(v___x_5360_);
if (v_isSharedCheck_5406_ == 0)
{
v___x_5401_ = v___x_5360_;
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_a_5399_);
lean_dec(v___x_5360_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5406_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v___x_5404_; 
if (v_isShared_5402_ == 0)
{
v___x_5404_ = v___x_5401_;
goto v_reusejp_5403_;
}
else
{
lean_object* v_reuseFailAlloc_5405_; 
v_reuseFailAlloc_5405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5405_, 0, v_a_5399_);
v___x_5404_ = v_reuseFailAlloc_5405_;
goto v_reusejp_5403_;
}
v_reusejp_5403_:
{
return v___x_5404_;
}
}
}
}
else
{
lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; 
lean_dec(v_a_5357_);
lean_dec_ref(v_scope_5322_);
lean_dec(v_goal_5321_);
lean_dec_ref(v_info_5315_);
v___x_5407_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___closed__9);
v___x_5408_ = l_Lean_indentExpr(v___x_5320_);
v___x_5409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5409_, 0, v___x_5407_);
lean_ctor_set(v___x_5409_, 1, v___x_5408_);
v___x_5410_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5409_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
return v___x_5410_;
}
}
else
{
lean_object* v_a_5411_; lean_object* v___x_5413_; uint8_t v_isShared_5414_; uint8_t v_isSharedCheck_5418_; 
lean_dec_ref(v_scope_5322_);
lean_dec(v_goal_5321_);
lean_dec_ref(v___x_5320_);
lean_dec_ref(v_info_5315_);
v_a_5411_ = lean_ctor_get(v___x_5356_, 0);
v_isSharedCheck_5418_ = !lean_is_exclusive(v___x_5356_);
if (v_isSharedCheck_5418_ == 0)
{
v___x_5413_ = v___x_5356_;
v_isShared_5414_ = v_isSharedCheck_5418_;
goto v_resetjp_5412_;
}
else
{
lean_inc(v_a_5411_);
lean_dec(v___x_5356_);
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
else
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
lean_dec_ref(v_scope_5322_);
lean_dec(v_goal_5321_);
lean_dec_ref(v___x_5320_);
lean_dec_ref(v_info_5315_);
v_a_5419_ = lean_ctor_get(v___x_5352_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5352_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___x_5352_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___x_5352_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5419_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
else
{
lean_object* v___x_5427_; lean_object* v___x_5429_; 
lean_dec(v_a_5336_);
lean_dec_ref(v_scope_5322_);
lean_dec_ref(v___x_5320_);
lean_dec_ref(v___x_5319_);
lean_dec_ref(v___x_5318_);
lean_dec_ref(v___x_5317_);
lean_dec_ref(v___x_5316_);
v___x_5427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5427_, 0, v_goal_5321_);
lean_ctor_set(v___x_5427_, 1, v_info_5315_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 0, v___x_5427_);
v___x_5429_ = v___x_5338_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v___x_5427_);
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
lean_dec_ref(v_scope_5322_);
lean_dec(v_goal_5321_);
lean_dec_ref(v___x_5320_);
lean_dec_ref(v___x_5319_);
lean_dec_ref(v___x_5318_);
lean_dec_ref(v___x_5317_);
lean_dec_ref(v___x_5316_);
lean_dec_ref(v_info_5315_);
v_a_5432_ = lean_ctor_get(v___x_5335_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5335_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5335_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5335_);
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
else
{
lean_object* v_strippedProg_5440_; lean_object* v___x_5441_; 
lean_dec_ref(v_scope_5322_);
lean_dec_ref(v___x_5319_);
lean_dec_ref(v___x_5318_);
lean_dec_ref(v___x_5317_);
lean_dec_ref(v___x_5316_);
v_strippedProg_5440_ = l_Lean_Expr_appArg_x21(v___x_5320_);
lean_dec_ref(v___x_5320_);
lean_inc_ref(v_strippedProg_5440_);
lean_inc_ref(v_info_5315_);
v___x_5441_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_5321_, v_info_5315_, v_strippedProg_5440_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, v___y_5333_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5462_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5444_ = v___x_5441_;
v_isShared_5445_ = v_isSharedCheck_5462_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5441_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5462_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v_head_5446_; lean_object* v_args_5447_; lean_object* v_excessArgs_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5461_; 
v_head_5446_ = lean_ctor_get(v_info_5315_, 0);
v_args_5447_ = lean_ctor_get(v_info_5315_, 1);
v_excessArgs_5448_ = lean_ctor_get(v_info_5315_, 2);
v_isSharedCheck_5461_ = !lean_is_exclusive(v_info_5315_);
if (v_isSharedCheck_5461_ == 0)
{
v___x_5450_ = v_info_5315_;
v_isShared_5451_ = v_isSharedCheck_5461_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_excessArgs_5448_);
lean_inc(v_args_5447_);
lean_inc(v_head_5446_);
lean_dec(v_info_5315_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5461_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5452_; lean_object* v___x_5453_; lean_object* v___x_5455_; 
v___x_5452_ = lean_unsigned_to_nat(7u);
v___x_5453_ = lean_array_set(v_args_5447_, v___x_5452_, v_strippedProg_5440_);
if (v_isShared_5451_ == 0)
{
lean_ctor_set(v___x_5450_, 1, v___x_5453_);
v___x_5455_ = v___x_5450_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5460_; 
v_reuseFailAlloc_5460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5460_, 0, v_head_5446_);
lean_ctor_set(v_reuseFailAlloc_5460_, 1, v___x_5453_);
lean_ctor_set(v_reuseFailAlloc_5460_, 2, v_excessArgs_5448_);
v___x_5455_ = v_reuseFailAlloc_5460_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
lean_object* v___x_5456_; lean_object* v___x_5458_; 
v___x_5456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5456_, 0, v_a_5442_);
lean_ctor_set(v___x_5456_, 1, v___x_5455_);
if (v_isShared_5445_ == 0)
{
lean_ctor_set(v___x_5444_, 0, v___x_5456_);
v___x_5458_ = v___x_5444_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5459_; 
v_reuseFailAlloc_5459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5459_, 0, v___x_5456_);
v___x_5458_ = v_reuseFailAlloc_5459_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
return v___x_5458_;
}
}
}
}
}
else
{
lean_object* v_a_5463_; lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5470_; 
lean_dec_ref(v_strippedProg_5440_);
lean_dec_ref(v_info_5315_);
v_a_5463_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5470_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5470_ == 0)
{
v___x_5465_ = v___x_5441_;
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
else
{
lean_inc(v_a_5463_);
lean_dec(v___x_5441_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5470_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v___x_5468_; 
if (v_isShared_5466_ == 0)
{
v___x_5468_ = v___x_5465_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5469_; 
v_reuseFailAlloc_5469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5469_, 0, v_a_5463_);
v___x_5468_ = v_reuseFailAlloc_5469_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
return v___x_5468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___boxed(lean_object** _args){
lean_object* v___x_5471_ = _args[0];
lean_object* v_info_5472_ = _args[1];
lean_object* v___x_5473_ = _args[2];
lean_object* v___x_5474_ = _args[3];
lean_object* v___x_5475_ = _args[4];
lean_object* v___x_5476_ = _args[5];
lean_object* v___x_5477_ = _args[6];
lean_object* v_goal_5478_ = _args[7];
lean_object* v_scope_5479_ = _args[8];
lean_object* v___y_5480_ = _args[9];
lean_object* v___y_5481_ = _args[10];
lean_object* v___y_5482_ = _args[11];
lean_object* v___y_5483_ = _args[12];
lean_object* v___y_5484_ = _args[13];
lean_object* v___y_5485_ = _args[14];
lean_object* v___y_5486_ = _args[15];
lean_object* v___y_5487_ = _args[16];
lean_object* v___y_5488_ = _args[17];
lean_object* v___y_5489_ = _args[18];
lean_object* v___y_5490_ = _args[19];
lean_object* v___y_5491_ = _args[20];
_start:
{
uint8_t v___x_25457__boxed_5492_; lean_object* v_res_5493_; 
v___x_25457__boxed_5492_ = lean_unbox(v___x_5471_);
v_res_5493_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0(v___x_25457__boxed_5492_, v_info_5472_, v___x_5473_, v___x_5474_, v___x_5475_, v___x_5476_, v___x_5477_, v_goal_5478_, v_scope_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
lean_dec(v___y_5488_);
lean_dec_ref(v___y_5487_);
lean_dec(v___y_5486_);
lean_dec_ref(v___y_5485_);
lean_dec(v___y_5484_);
lean_dec_ref(v___y_5483_);
lean_dec(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
return v_res_5493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(lean_object* v_scope_5502_, lean_object* v_goal_5503_, lean_object* v_info_5504_, lean_object* v_a_5505_, lean_object* v_a_5506_, lean_object* v_a_5507_, lean_object* v_a_5508_, lean_object* v_a_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; uint8_t v___x_5524_; lean_object* v___x_5525_; lean_object* v___y_5526_; lean_object* v___x_5527_; 
v___x_5517_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_5504_);
v___x_5518_ = l_Lean_Expr_getAppFn(v___x_5517_);
v___x_5519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0));
v___x_5520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1));
v___x_5521_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2));
v___x_5522_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__0));
v___x_5523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___closed__2));
v___x_5524_ = l_Lean_Expr_isConstOf(v___x_5518_, v___x_5523_);
lean_dec_ref(v___x_5518_);
v___x_5525_ = lean_box(v___x_5524_);
lean_inc(v_goal_5503_);
v___y_5526_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___lam__0___boxed), 21, 9);
lean_closure_set(v___y_5526_, 0, v___x_5525_);
lean_closure_set(v___y_5526_, 1, v_info_5504_);
lean_closure_set(v___y_5526_, 2, v___x_5519_);
lean_closure_set(v___y_5526_, 3, v___x_5520_);
lean_closure_set(v___y_5526_, 4, v___x_5521_);
lean_closure_set(v___y_5526_, 5, v___x_5522_);
lean_closure_set(v___y_5526_, 6, v___x_5517_);
lean_closure_set(v___y_5526_, 7, v_goal_5503_);
lean_closure_set(v___y_5526_, 8, v_scope_5502_);
v___x_5527_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_5503_, v___y_5526_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_, v_a_5509_, v_a_5510_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_);
return v___x_5527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame___boxed(lean_object* v_scope_5528_, lean_object* v_goal_5529_, lean_object* v_info_5530_, lean_object* v_a_5531_, lean_object* v_a_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_){
_start:
{
lean_object* v_res_5543_; 
v_res_5543_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(v_scope_5528_, v_goal_5529_, v_info_5530_, v_a_5531_, v_a_5532_, v_a_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_, v_a_5539_, v_a_5540_, v_a_5541_);
lean_dec(v_a_5541_);
lean_dec_ref(v_a_5540_);
lean_dec(v_a_5539_);
lean_dec_ref(v_a_5538_);
lean_dec(v_a_5537_);
lean_dec_ref(v_a_5536_);
lean_dec(v_a_5535_);
lean_dec_ref(v_a_5534_);
lean_dec(v_a_5533_);
lean_dec(v_a_5532_);
lean_dec_ref(v_a_5531_);
return v_res_5543_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5545_; lean_object* v___x_5546_; 
v___x_5545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_5546_ = l_Lean_stringToMessageData(v___x_5545_);
return v___x_5546_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
v___x_5548_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2));
v___x_5549_ = l_Lean_stringToMessageData(v___x_5548_);
return v___x_5549_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5551_; lean_object* v___x_5552_; 
v___x_5551_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_5552_ = l_Lean_stringToMessageData(v___x_5551_);
return v___x_5552_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5554_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6));
v___x_5555_ = l_Lean_stringToMessageData(v___x_5554_);
return v___x_5555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_5558_, lean_object* v_scope_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_){
_start:
{
lean_object* v_scope_5573_; lean_object* v_gs_5574_; lean_object* v_g_5578_; lean_object* v_gs_5584_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5594_; lean_object* v_g_5595_; lean_object* v___y_5601_; lean_object* v_gs_5602_; lean_object* v___y_5606_; lean_object* v_g_5607_; lean_object* v___y_5608_; lean_object* v___y_5630_; lean_object* v___y_5631_; lean_object* v___y_5632_; lean_object* v___y_5633_; lean_object* v___y_5634_; lean_object* v___y_5635_; lean_object* v___y_5636_; lean_object* v___y_5637_; lean_object* v___y_5638_; lean_object* v___y_5639_; lean_object* v___y_5640_; lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v___y_5668_; lean_object* v___y_5669_; lean_object* v___y_5670_; lean_object* v___y_5671_; lean_object* v___y_5672_; lean_object* v___y_5673_; lean_object* v___y_5674_; lean_object* v___y_5675_; lean_object* v___y_5676_; lean_object* v___y_5677_; lean_object* v___y_5678_; lean_object* v___y_5679_; lean_object* v___y_5680_; lean_object* v___y_5681_; lean_object* v___y_5682_; lean_object* v___x_5795_; 
v___x_5795_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_5561_);
if (lean_obj_tag(v___x_5795_) == 0)
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_6033_; 
v_a_5796_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_6033_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_6033_ == 0)
{
v___x_5798_ = v___x_5795_;
v_isShared_5799_ = v_isSharedCheck_6033_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5795_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_6033_;
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
lean_inc(v_goal_5558_);
v___x_5801_ = l_Lean_MVarId_getType(v_goal_5558_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_5801_) == 0)
{
lean_object* v_a_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_6020_; 
v_a_5802_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_6020_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_6020_ == 0)
{
v___x_5804_ = v___x_5801_;
v_isShared_5805_ = v_isSharedCheck_6020_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_a_5802_);
lean_dec(v___x_5801_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_6020_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
lean_object* v_options_5812_; lean_object* v_inheritedTraceOptions_5813_; uint8_t v_hasTrace_5814_; lean_object* v___x_5815_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___y_5821_; lean_object* v___y_5822_; lean_object* v___y_5823_; lean_object* v___y_5824_; lean_object* v___y_5825_; lean_object* v___y_5826_; lean_object* v___y_5827_; 
v_options_5812_ = lean_ctor_get(v___y_5569_, 2);
v_inheritedTraceOptions_5813_ = lean_ctor_get(v___y_5569_, 13);
v_hasTrace_5814_ = lean_ctor_get_uint8(v_options_5812_, sizeof(void*)*1);
v___x_5815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_5814_ == 0)
{
v___y_5817_ = v___y_5560_;
v___y_5818_ = v___y_5561_;
v___y_5819_ = v___y_5562_;
v___y_5820_ = v___y_5563_;
v___y_5821_ = v___y_5564_;
v___y_5822_ = v___y_5565_;
v___y_5823_ = v___y_5566_;
v___y_5824_ = v___y_5567_;
v___y_5825_ = v___y_5568_;
v___y_5826_ = v___y_5569_;
v___y_5827_ = v___y_5570_;
goto v___jp_5816_;
}
else
{
lean_object* v___x_6006_; uint8_t v___x_6007_; 
v___x_6006_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_6007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5813_, v_options_5812_, v___x_6006_);
if (v___x_6007_ == 0)
{
v___y_5817_ = v___y_5560_;
v___y_5818_ = v___y_5561_;
v___y_5819_ = v___y_5562_;
v___y_5820_ = v___y_5563_;
v___y_5821_ = v___y_5564_;
v___y_5822_ = v___y_5565_;
v___y_5823_ = v___y_5566_;
v___y_5824_ = v___y_5567_;
v___y_5825_ = v___y_5568_;
v___y_5826_ = v___y_5569_;
v___y_5827_ = v___y_5570_;
goto v___jp_5816_;
}
else
{
lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; 
v___x_6008_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_5802_);
v___x_6009_ = l_Lean_MessageData_ofExpr(v_a_5802_);
v___x_6010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6010_, 0, v___x_6008_);
lean_ctor_set(v___x_6010_, 1, v___x_6009_);
v___x_6011_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5815_, v___x_6010_, v___y_5567_, v___y_5568_, v___y_5569_, v___y_5570_);
if (lean_obj_tag(v___x_6011_) == 0)
{
lean_dec_ref_known(v___x_6011_, 1);
v___y_5817_ = v___y_5560_;
v___y_5818_ = v___y_5561_;
v___y_5819_ = v___y_5562_;
v___y_5820_ = v___y_5563_;
v___y_5821_ = v___y_5564_;
v___y_5822_ = v___y_5565_;
v___y_5823_ = v___y_5566_;
v___y_5824_ = v___y_5567_;
v___y_5825_ = v___y_5568_;
v___y_5826_ = v___y_5569_;
v___y_5827_ = v___y_5570_;
goto v___jp_5816_;
}
else
{
lean_object* v_a_6012_; lean_object* v___x_6014_; uint8_t v_isShared_6015_; uint8_t v_isSharedCheck_6019_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_6012_ = lean_ctor_get(v___x_6011_, 0);
v_isSharedCheck_6019_ = !lean_is_exclusive(v___x_6011_);
if (v_isSharedCheck_6019_ == 0)
{
v___x_6014_ = v___x_6011_;
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
else
{
lean_inc(v_a_6012_);
lean_dec(v___x_6011_);
v___x_6014_ = lean_box(0);
v_isShared_6015_ = v_isSharedCheck_6019_;
goto v_resetjp_6013_;
}
v_resetjp_6013_:
{
lean_object* v___x_6017_; 
if (v_isShared_6015_ == 0)
{
v___x_6017_ = v___x_6014_;
goto v_reusejp_6016_;
}
else
{
lean_object* v_reuseFailAlloc_6018_; 
v_reuseFailAlloc_6018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6018_, 0, v_a_6012_);
v___x_6017_ = v_reuseFailAlloc_6018_;
goto v_reusejp_6016_;
}
v_reusejp_6016_:
{
return v___x_6017_;
}
}
}
}
}
v___jp_5806_:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5810_; 
v___x_5807_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_5807_, 0, v_a_5802_);
v___x_5808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5808_, 0, v___x_5807_);
if (v_isShared_5805_ == 0)
{
lean_ctor_set(v___x_5804_, 0, v___x_5808_);
v___x_5810_ = v___x_5804_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v___x_5808_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
v___jp_5816_:
{
lean_object* v___x_5828_; 
lean_inc(v_goal_5558_);
v___x_5828_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_5558_, v_a_5802_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5828_) == 0)
{
lean_object* v_a_5829_; 
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5829_);
lean_dec_ref_known(v___x_5828_, 1);
if (lean_obj_tag(v_a_5829_) == 1)
{
lean_object* v_val_5830_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_val_5830_ = lean_ctor_get(v_a_5829_, 0);
lean_inc(v_val_5830_);
lean_dec_ref_known(v_a_5829_, 1);
v_gs_5584_ = v_val_5830_;
goto v___jp_5583_;
}
else
{
lean_object* v___x_5831_; 
lean_dec(v_a_5829_);
lean_inc(v_a_5802_);
lean_inc(v_goal_5558_);
v___x_5831_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_5558_, v_a_5802_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
lean_inc(v_a_5832_);
lean_dec_ref_known(v___x_5831_, 1);
if (lean_obj_tag(v_a_5832_) == 1)
{
lean_object* v_val_5833_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_val_5833_ = lean_ctor_get(v_a_5832_, 0);
lean_inc(v_val_5833_);
lean_dec_ref_known(v_a_5832_, 1);
v_g_5578_ = v_val_5833_;
goto v___jp_5577_;
}
else
{
lean_object* v___x_5834_; 
lean_dec(v_a_5832_);
lean_inc(v_goal_5558_);
v___x_5834_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_5558_, v_a_5802_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5834_) == 0)
{
lean_object* v_a_5835_; 
v_a_5835_ = lean_ctor_get(v___x_5834_, 0);
lean_inc(v_a_5835_);
lean_dec_ref_known(v___x_5834_, 1);
if (lean_obj_tag(v_a_5835_) == 1)
{
lean_object* v_val_5836_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_val_5836_ = lean_ctor_get(v_a_5835_, 0);
lean_inc(v_val_5836_);
lean_dec_ref_known(v_a_5835_, 1);
v_g_5578_ = v_val_5836_;
goto v___jp_5577_;
}
else
{
lean_object* v___x_5837_; 
lean_dec(v_a_5835_);
lean_inc(v_a_5802_);
lean_inc(v_goal_5558_);
v___x_5837_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_5558_, v_a_5802_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5837_) == 0)
{
lean_object* v_a_5838_; 
v_a_5838_ = lean_ctor_get(v___x_5837_, 0);
lean_inc(v_a_5838_);
lean_dec_ref_known(v___x_5837_, 1);
if (lean_obj_tag(v_a_5838_) == 1)
{
lean_object* v_val_5839_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_val_5839_ = lean_ctor_get(v_a_5838_, 0);
lean_inc(v_val_5839_);
lean_dec_ref_known(v_a_5838_, 1);
v_g_5578_ = v_val_5839_;
goto v___jp_5577_;
}
else
{
lean_object* v___x_5840_; 
lean_dec(v_a_5838_);
lean_inc(v_a_5802_);
lean_inc(v_goal_5558_);
lean_inc_ref(v_scope_5559_);
v___x_5840_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_5559_, v_goal_5558_, v_a_5802_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5840_) == 0)
{
lean_object* v_a_5841_; 
v_a_5841_ = lean_ctor_get(v___x_5840_, 0);
lean_inc(v_a_5841_);
lean_dec_ref_known(v___x_5840_, 1);
if (lean_obj_tag(v_a_5841_) == 1)
{
lean_object* v_val_5842_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_val_5842_ = lean_ctor_get(v_a_5841_, 0);
lean_inc(v_val_5842_);
lean_dec_ref_known(v_a_5841_, 1);
v_gs_5584_ = v_val_5842_;
goto v___jp_5583_;
}
else
{
lean_object* v___x_5843_; uint8_t v___x_5844_; 
lean_dec(v_a_5841_);
lean_inc(v_a_5802_);
v___x_5843_ = l_Lean_Expr_cleanupAnnotations(v_a_5802_);
v___x_5844_ = l_Lean_Expr_isApp(v___x_5843_);
if (v___x_5844_ == 0)
{
lean_dec_ref(v___x_5843_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
goto v___jp_5806_;
}
else
{
lean_object* v_arg_5845_; lean_object* v___x_5846_; uint8_t v___x_5847_; 
v_arg_5845_ = lean_ctor_get(v___x_5843_, 1);
lean_inc_ref(v_arg_5845_);
v___x_5846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5843_);
v___x_5847_ = l_Lean_Expr_isApp(v___x_5846_);
if (v___x_5847_ == 0)
{
lean_dec_ref(v___x_5846_);
lean_dec_ref(v_arg_5845_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
goto v___jp_5806_;
}
else
{
lean_object* v_arg_5848_; lean_object* v___x_5849_; uint8_t v___x_5850_; 
v_arg_5848_ = lean_ctor_get(v___x_5846_, 1);
lean_inc_ref(v_arg_5848_);
v___x_5849_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5846_);
v___x_5850_ = l_Lean_Expr_isApp(v___x_5849_);
if (v___x_5850_ == 0)
{
lean_dec_ref(v___x_5849_);
lean_dec_ref(v_arg_5848_);
lean_dec_ref(v_arg_5845_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
goto v___jp_5806_;
}
else
{
lean_object* v_arg_5851_; lean_object* v___x_5852_; uint8_t v___x_5853_; 
v_arg_5851_ = lean_ctor_get(v___x_5849_, 1);
lean_inc_ref(v_arg_5851_);
v___x_5852_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5849_);
v___x_5853_ = l_Lean_Expr_isApp(v___x_5852_);
if (v___x_5853_ == 0)
{
lean_dec_ref(v___x_5852_);
lean_dec_ref(v_arg_5851_);
lean_dec_ref(v_arg_5848_);
lean_dec_ref(v_arg_5845_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
goto v___jp_5806_;
}
else
{
lean_object* v_arg_5854_; lean_object* v___x_5855_; lean_object* v___x_5856_; uint8_t v___x_5857_; 
v_arg_5854_ = lean_ctor_get(v___x_5852_, 1);
lean_inc_ref(v_arg_5854_);
v___x_5855_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5852_);
v___x_5856_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_5857_ = l_Lean_Expr_isConstOf(v___x_5855_, v___x_5856_);
lean_dec_ref(v___x_5855_);
if (v___x_5857_ == 0)
{
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec_ref(v_arg_5848_);
lean_dec_ref(v_arg_5845_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
goto v___jp_5806_;
}
else
{
lean_object* v___x_5858_; 
lean_del_object(v___x_5804_);
v___x_5858_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_5848_, v___y_5825_);
if (lean_obj_tag(v___x_5858_) == 0)
{
lean_object* v_a_5859_; lean_object* v___x_5860_; 
v_a_5859_ = lean_ctor_get(v___x_5858_, 0);
lean_inc(v_a_5859_);
lean_dec_ref_known(v___x_5858_, 1);
v___x_5860_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_5845_, v___y_5825_);
if (lean_obj_tag(v___x_5860_) == 0)
{
lean_object* v_a_5861_; lean_object* v___x_5862_; 
v_a_5861_ = lean_ctor_get(v___x_5860_, 0);
lean_inc(v_a_5861_);
lean_dec_ref_known(v___x_5860_, 1);
lean_inc(v_goal_5558_);
v___x_5862_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_5558_, v___y_5817_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5862_) == 0)
{
lean_object* v_a_5863_; 
v_a_5863_ = lean_ctor_get(v___x_5862_, 0);
lean_inc(v_a_5863_);
lean_dec_ref_known(v___x_5862_, 1);
if (lean_obj_tag(v_a_5863_) == 1)
{
lean_object* v_val_5864_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_val_5864_ = lean_ctor_get(v_a_5863_, 0);
lean_inc(v_val_5864_);
lean_dec_ref_known(v_a_5863_, 1);
v_gs_5584_ = v_val_5864_;
goto v___jp_5583_;
}
else
{
lean_object* v___x_5865_; 
lean_dec(v_a_5863_);
lean_inc(v_a_5802_);
lean_inc(v_a_5859_);
lean_inc(v_goal_5558_);
lean_inc_ref(v_scope_5559_);
v___x_5865_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_5559_, v_goal_5558_, v_arg_5854_, v_a_5859_, v_a_5802_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5865_) == 0)
{
lean_object* v_a_5866_; 
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5866_);
lean_dec_ref_known(v___x_5865_, 1);
if (lean_obj_tag(v_a_5866_) == 1)
{
lean_object* v_val_5867_; lean_object* v_fst_5868_; lean_object* v_snd_5869_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_val_5867_ = lean_ctor_get(v_a_5866_, 0);
lean_inc(v_val_5867_);
lean_dec_ref_known(v_a_5866_, 1);
v_fst_5868_ = lean_ctor_get(v_val_5867_, 0);
lean_inc(v_fst_5868_);
v_snd_5869_ = lean_ctor_get(v_val_5867_, 1);
lean_inc(v_snd_5869_);
lean_dec(v_val_5867_);
v_scope_5573_ = v_fst_5868_;
v_gs_5574_ = v_snd_5869_;
goto v___jp_5572_;
}
else
{
lean_object* v___x_5870_; 
lean_dec(v_a_5866_);
lean_inc(v_goal_5558_);
v___x_5870_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_5559_, v_goal_5558_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5870_) == 0)
{
lean_object* v_a_5871_; lean_object* v___x_5872_; 
v_a_5871_ = lean_ctor_get(v___x_5870_, 0);
lean_inc(v_a_5871_);
lean_dec_ref_known(v___x_5870_, 1);
lean_inc(v_a_5861_);
lean_inc(v_a_5859_);
lean_inc_ref(v_arg_5854_);
lean_inc(v_goal_5558_);
v___x_5872_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_5558_, v_a_5802_, v_arg_5854_, v_arg_5851_, v_a_5859_, v_a_5861_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5872_) == 0)
{
lean_object* v_a_5873_; 
v_a_5873_ = lean_ctor_get(v___x_5872_, 0);
lean_inc(v_a_5873_);
lean_dec_ref_known(v___x_5872_, 1);
if (lean_obj_tag(v_a_5873_) == 1)
{
lean_object* v_val_5874_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec(v_goal_5558_);
v_val_5874_ = lean_ctor_get(v_a_5873_, 0);
lean_inc(v_val_5874_);
lean_dec_ref_known(v_a_5873_, 1);
v___y_5594_ = v_a_5871_;
v_g_5595_ = v_val_5874_;
goto v___jp_5593_;
}
else
{
lean_object* v___x_5875_; 
lean_dec(v_a_5873_);
lean_inc(v_a_5861_);
lean_inc(v_goal_5558_);
v___x_5875_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_5558_, v_a_5861_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5875_) == 0)
{
lean_object* v_a_5876_; 
v_a_5876_ = lean_ctor_get(v___x_5875_, 0);
lean_inc(v_a_5876_);
lean_dec_ref_known(v___x_5875_, 1);
if (lean_obj_tag(v_a_5876_) == 1)
{
lean_object* v_val_5877_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec(v_goal_5558_);
v_val_5877_ = lean_ctor_get(v_a_5876_, 0);
lean_inc(v_val_5877_);
lean_dec_ref_known(v_a_5876_, 1);
v___y_5601_ = v_a_5871_;
v_gs_5602_ = v_val_5877_;
goto v___jp_5600_;
}
else
{
lean_object* v___x_5878_; 
lean_dec(v_a_5876_);
lean_inc(v_a_5861_);
lean_inc(v_a_5859_);
lean_inc(v_goal_5558_);
lean_inc(v_a_5871_);
v___x_5878_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_a_5871_, v_goal_5558_, v_arg_5854_, v_a_5859_, v_a_5861_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
lean_dec_ref(v_arg_5854_);
if (lean_obj_tag(v___x_5878_) == 0)
{
lean_object* v_a_5879_; 
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc(v_a_5879_);
lean_dec_ref_known(v___x_5878_, 1);
if (lean_obj_tag(v_a_5879_) == 1)
{
lean_object* v_val_5880_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec(v_goal_5558_);
v_val_5880_ = lean_ctor_get(v_a_5879_, 0);
lean_inc(v_val_5880_);
lean_dec_ref_known(v_a_5879_, 1);
v___y_5601_ = v_a_5871_;
v_gs_5602_ = v_val_5880_;
goto v___jp_5600_;
}
else
{
lean_object* v___x_5881_; 
lean_dec(v_a_5879_);
lean_inc(v_a_5861_);
v___x_5881_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(v_a_5861_);
if (lean_obj_tag(v___x_5881_) == 1)
{
lean_object* v_options_5882_; uint8_t v_hasTrace_5883_; 
v_options_5882_ = lean_ctor_get(v___y_5826_, 2);
v_hasTrace_5883_ = lean_ctor_get_uint8(v_options_5882_, sizeof(void*)*1);
if (v_hasTrace_5883_ == 0)
{
lean_object* v_val_5884_; 
v_val_5884_ = lean_ctor_get(v___x_5881_, 0);
lean_inc(v_val_5884_);
lean_dec_ref_known(v___x_5881_, 1);
v___y_5668_ = v_a_5861_;
v___y_5669_ = v_a_5871_;
v___y_5670_ = v_val_5884_;
v___y_5671_ = v_a_5859_;
v___y_5672_ = v___y_5817_;
v___y_5673_ = v___y_5818_;
v___y_5674_ = v___y_5819_;
v___y_5675_ = v___y_5820_;
v___y_5676_ = v___y_5821_;
v___y_5677_ = v___y_5822_;
v___y_5678_ = v___y_5823_;
v___y_5679_ = v___y_5824_;
v___y_5680_ = v___y_5825_;
v___y_5681_ = v___y_5826_;
v___y_5682_ = v___y_5827_;
goto v___jp_5667_;
}
else
{
lean_object* v_val_5885_; lean_object* v_inheritedTraceOptions_5886_; lean_object* v___x_5887_; uint8_t v___x_5888_; 
v_val_5885_ = lean_ctor_get(v___x_5881_, 0);
lean_inc(v_val_5885_);
lean_dec_ref_known(v___x_5881_, 1);
v_inheritedTraceOptions_5886_ = lean_ctor_get(v___y_5826_, 13);
v___x_5887_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_5888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5886_, v_options_5882_, v___x_5887_);
if (v___x_5888_ == 0)
{
v___y_5668_ = v_a_5861_;
v___y_5669_ = v_a_5871_;
v___y_5670_ = v_val_5885_;
v___y_5671_ = v_a_5859_;
v___y_5672_ = v___y_5817_;
v___y_5673_ = v___y_5818_;
v___y_5674_ = v___y_5819_;
v___y_5675_ = v___y_5820_;
v___y_5676_ = v___y_5821_;
v___y_5677_ = v___y_5822_;
v___y_5678_ = v___y_5823_;
v___y_5679_ = v___y_5824_;
v___y_5680_ = v___y_5825_;
v___y_5681_ = v___y_5826_;
v___y_5682_ = v___y_5827_;
goto v___jp_5667_;
}
else
{
lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
v___x_5889_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5);
v___x_5890_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_val_5885_);
v___x_5891_ = l_Lean_MessageData_ofExpr(v___x_5890_);
v___x_5892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5889_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_5815_, v___x_5892_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_dec_ref_known(v___x_5893_, 1);
v___y_5668_ = v_a_5861_;
v___y_5669_ = v_a_5871_;
v___y_5670_ = v_val_5885_;
v___y_5671_ = v_a_5859_;
v___y_5672_ = v___y_5817_;
v___y_5673_ = v___y_5818_;
v___y_5674_ = v___y_5819_;
v___y_5675_ = v___y_5820_;
v___y_5676_ = v___y_5821_;
v___y_5677_ = v___y_5822_;
v___y_5678_ = v___y_5823_;
v___y_5679_ = v___y_5824_;
v___y_5680_ = v___y_5825_;
v___y_5681_ = v___y_5826_;
v___y_5682_ = v___y_5827_;
goto v___jp_5667_;
}
else
{
lean_object* v_a_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5901_; 
lean_dec(v_val_5885_);
lean_dec(v_a_5871_);
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec(v_goal_5558_);
v_a_5894_ = lean_ctor_get(v___x_5893_, 0);
v_isSharedCheck_5901_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5896_ = v___x_5893_;
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_a_5894_);
lean_dec(v___x_5893_);
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
}
}
else
{
lean_dec(v___x_5881_);
lean_dec(v_a_5871_);
lean_dec(v_goal_5558_);
v___y_5588_ = v_a_5861_;
v___y_5589_ = v_a_5859_;
goto v___jp_5587_;
}
}
}
else
{
lean_object* v_a_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5909_; 
lean_dec(v_a_5871_);
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec(v_goal_5558_);
v_a_5902_ = lean_ctor_get(v___x_5878_, 0);
v_isSharedCheck_5909_ = !lean_is_exclusive(v___x_5878_);
if (v_isSharedCheck_5909_ == 0)
{
v___x_5904_ = v___x_5878_;
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_a_5902_);
lean_dec(v___x_5878_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5907_; 
if (v_isShared_5905_ == 0)
{
v___x_5907_ = v___x_5904_;
goto v_reusejp_5906_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_a_5902_);
v___x_5907_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5906_;
}
v_reusejp_5906_:
{
return v___x_5907_;
}
}
}
}
}
else
{
lean_object* v_a_5910_; lean_object* v___x_5912_; uint8_t v_isShared_5913_; uint8_t v_isSharedCheck_5917_; 
lean_dec(v_a_5871_);
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec(v_goal_5558_);
v_a_5910_ = lean_ctor_get(v___x_5875_, 0);
v_isSharedCheck_5917_ = !lean_is_exclusive(v___x_5875_);
if (v_isSharedCheck_5917_ == 0)
{
v___x_5912_ = v___x_5875_;
v_isShared_5913_ = v_isSharedCheck_5917_;
goto v_resetjp_5911_;
}
else
{
lean_inc(v_a_5910_);
lean_dec(v___x_5875_);
v___x_5912_ = lean_box(0);
v_isShared_5913_ = v_isSharedCheck_5917_;
goto v_resetjp_5911_;
}
v_resetjp_5911_:
{
lean_object* v___x_5915_; 
if (v_isShared_5913_ == 0)
{
v___x_5915_ = v___x_5912_;
goto v_reusejp_5914_;
}
else
{
lean_object* v_reuseFailAlloc_5916_; 
v_reuseFailAlloc_5916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_a_5910_);
v___x_5915_ = v_reuseFailAlloc_5916_;
goto v_reusejp_5914_;
}
v_reusejp_5914_:
{
return v___x_5915_;
}
}
}
}
}
else
{
lean_object* v_a_5918_; lean_object* v___x_5920_; uint8_t v_isShared_5921_; uint8_t v_isSharedCheck_5925_; 
lean_dec(v_a_5871_);
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec(v_goal_5558_);
v_a_5918_ = lean_ctor_get(v___x_5872_, 0);
v_isSharedCheck_5925_ = !lean_is_exclusive(v___x_5872_);
if (v_isSharedCheck_5925_ == 0)
{
v___x_5920_ = v___x_5872_;
v_isShared_5921_ = v_isSharedCheck_5925_;
goto v_resetjp_5919_;
}
else
{
lean_inc(v_a_5918_);
lean_dec(v___x_5872_);
v___x_5920_ = lean_box(0);
v_isShared_5921_ = v_isSharedCheck_5925_;
goto v_resetjp_5919_;
}
v_resetjp_5919_:
{
lean_object* v___x_5923_; 
if (v_isShared_5921_ == 0)
{
v___x_5923_ = v___x_5920_;
goto v_reusejp_5922_;
}
else
{
lean_object* v_reuseFailAlloc_5924_; 
v_reuseFailAlloc_5924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5924_, 0, v_a_5918_);
v___x_5923_ = v_reuseFailAlloc_5924_;
goto v_reusejp_5922_;
}
v_reusejp_5922_:
{
return v___x_5923_;
}
}
}
}
else
{
lean_object* v_a_5926_; lean_object* v___x_5928_; uint8_t v_isShared_5929_; uint8_t v_isSharedCheck_5933_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec(v_a_5802_);
lean_dec(v_goal_5558_);
v_a_5926_ = lean_ctor_get(v___x_5870_, 0);
v_isSharedCheck_5933_ = !lean_is_exclusive(v___x_5870_);
if (v_isSharedCheck_5933_ == 0)
{
v___x_5928_ = v___x_5870_;
v_isShared_5929_ = v_isSharedCheck_5933_;
goto v_resetjp_5927_;
}
else
{
lean_inc(v_a_5926_);
lean_dec(v___x_5870_);
v___x_5928_ = lean_box(0);
v_isShared_5929_ = v_isSharedCheck_5933_;
goto v_resetjp_5927_;
}
v_resetjp_5927_:
{
lean_object* v___x_5931_; 
if (v_isShared_5929_ == 0)
{
v___x_5931_ = v___x_5928_;
goto v_reusejp_5930_;
}
else
{
lean_object* v_reuseFailAlloc_5932_; 
v_reuseFailAlloc_5932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5932_, 0, v_a_5926_);
v___x_5931_ = v_reuseFailAlloc_5932_;
goto v_reusejp_5930_;
}
v_reusejp_5930_:
{
return v___x_5931_;
}
}
}
}
}
else
{
lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5941_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5934_ = lean_ctor_get(v___x_5865_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v___x_5865_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5936_ = v___x_5865_;
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5865_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v___x_5939_; 
if (v_isShared_5937_ == 0)
{
v___x_5939_ = v___x_5936_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5934_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
}
}
else
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5949_; 
lean_dec(v_a_5861_);
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5942_ = lean_ctor_get(v___x_5862_, 0);
v_isSharedCheck_5949_ = !lean_is_exclusive(v___x_5862_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5944_ = v___x_5862_;
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5862_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
if (v_isShared_5945_ == 0)
{
v___x_5947_ = v___x_5944_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5942_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
else
{
lean_object* v_a_5950_; lean_object* v___x_5952_; uint8_t v_isShared_5953_; uint8_t v_isSharedCheck_5957_; 
lean_dec(v_a_5859_);
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5950_ = lean_ctor_get(v___x_5860_, 0);
v_isSharedCheck_5957_ = !lean_is_exclusive(v___x_5860_);
if (v_isSharedCheck_5957_ == 0)
{
v___x_5952_ = v___x_5860_;
v_isShared_5953_ = v_isSharedCheck_5957_;
goto v_resetjp_5951_;
}
else
{
lean_inc(v_a_5950_);
lean_dec(v___x_5860_);
v___x_5952_ = lean_box(0);
v_isShared_5953_ = v_isSharedCheck_5957_;
goto v_resetjp_5951_;
}
v_resetjp_5951_:
{
lean_object* v___x_5955_; 
if (v_isShared_5953_ == 0)
{
v___x_5955_ = v___x_5952_;
goto v_reusejp_5954_;
}
else
{
lean_object* v_reuseFailAlloc_5956_; 
v_reuseFailAlloc_5956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5956_, 0, v_a_5950_);
v___x_5955_ = v_reuseFailAlloc_5956_;
goto v_reusejp_5954_;
}
v_reusejp_5954_:
{
return v___x_5955_;
}
}
}
}
else
{
lean_object* v_a_5958_; lean_object* v___x_5960_; uint8_t v_isShared_5961_; uint8_t v_isSharedCheck_5965_; 
lean_dec_ref(v_arg_5854_);
lean_dec_ref(v_arg_5851_);
lean_dec_ref(v_arg_5845_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5958_ = lean_ctor_get(v___x_5858_, 0);
v_isSharedCheck_5965_ = !lean_is_exclusive(v___x_5858_);
if (v_isSharedCheck_5965_ == 0)
{
v___x_5960_ = v___x_5858_;
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
else
{
lean_inc(v_a_5958_);
lean_dec(v___x_5858_);
v___x_5960_ = lean_box(0);
v_isShared_5961_ = v_isSharedCheck_5965_;
goto v_resetjp_5959_;
}
v_resetjp_5959_:
{
lean_object* v___x_5963_; 
if (v_isShared_5961_ == 0)
{
v___x_5963_ = v___x_5960_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5964_; 
v_reuseFailAlloc_5964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5964_, 0, v_a_5958_);
v___x_5963_ = v_reuseFailAlloc_5964_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
return v___x_5963_;
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
lean_object* v_a_5966_; lean_object* v___x_5968_; uint8_t v_isShared_5969_; uint8_t v_isSharedCheck_5973_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5966_ = lean_ctor_get(v___x_5840_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5968_ = v___x_5840_;
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
else
{
lean_inc(v_a_5966_);
lean_dec(v___x_5840_);
v___x_5968_ = lean_box(0);
v_isShared_5969_ = v_isSharedCheck_5973_;
goto v_resetjp_5967_;
}
v_resetjp_5967_:
{
lean_object* v___x_5971_; 
if (v_isShared_5969_ == 0)
{
v___x_5971_ = v___x_5968_;
goto v_reusejp_5970_;
}
else
{
lean_object* v_reuseFailAlloc_5972_; 
v_reuseFailAlloc_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5972_, 0, v_a_5966_);
v___x_5971_ = v_reuseFailAlloc_5972_;
goto v_reusejp_5970_;
}
v_reusejp_5970_:
{
return v___x_5971_;
}
}
}
}
}
else
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5981_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5974_ = lean_ctor_get(v___x_5837_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v___x_5837_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5976_ = v___x_5837_;
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5837_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
if (v_isShared_5977_ == 0)
{
v___x_5979_ = v___x_5976_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
v___x_5979_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
return v___x_5979_;
}
}
}
}
}
else
{
lean_object* v_a_5982_; lean_object* v___x_5984_; uint8_t v_isShared_5985_; uint8_t v_isSharedCheck_5989_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5982_ = lean_ctor_get(v___x_5834_, 0);
v_isSharedCheck_5989_ = !lean_is_exclusive(v___x_5834_);
if (v_isSharedCheck_5989_ == 0)
{
v___x_5984_ = v___x_5834_;
v_isShared_5985_ = v_isSharedCheck_5989_;
goto v_resetjp_5983_;
}
else
{
lean_inc(v_a_5982_);
lean_dec(v___x_5834_);
v___x_5984_ = lean_box(0);
v_isShared_5985_ = v_isSharedCheck_5989_;
goto v_resetjp_5983_;
}
v_resetjp_5983_:
{
lean_object* v___x_5987_; 
if (v_isShared_5985_ == 0)
{
v___x_5987_ = v___x_5984_;
goto v_reusejp_5986_;
}
else
{
lean_object* v_reuseFailAlloc_5988_; 
v_reuseFailAlloc_5988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5988_, 0, v_a_5982_);
v___x_5987_ = v_reuseFailAlloc_5988_;
goto v_reusejp_5986_;
}
v_reusejp_5986_:
{
return v___x_5987_;
}
}
}
}
}
else
{
lean_object* v_a_5990_; lean_object* v___x_5992_; uint8_t v_isShared_5993_; uint8_t v_isSharedCheck_5997_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5990_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5997_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5997_ == 0)
{
v___x_5992_ = v___x_5831_;
v_isShared_5993_ = v_isSharedCheck_5997_;
goto v_resetjp_5991_;
}
else
{
lean_inc(v_a_5990_);
lean_dec(v___x_5831_);
v___x_5992_ = lean_box(0);
v_isShared_5993_ = v_isSharedCheck_5997_;
goto v_resetjp_5991_;
}
v_resetjp_5991_:
{
lean_object* v___x_5995_; 
if (v_isShared_5993_ == 0)
{
v___x_5995_ = v___x_5992_;
goto v_reusejp_5994_;
}
else
{
lean_object* v_reuseFailAlloc_5996_; 
v_reuseFailAlloc_5996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_a_5990_);
v___x_5995_ = v_reuseFailAlloc_5996_;
goto v_reusejp_5994_;
}
v_reusejp_5994_:
{
return v___x_5995_;
}
}
}
}
}
else
{
lean_object* v_a_5998_; lean_object* v___x_6000_; uint8_t v_isShared_6001_; uint8_t v_isSharedCheck_6005_; 
lean_del_object(v___x_5804_);
lean_dec(v_a_5802_);
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_5998_ = lean_ctor_get(v___x_5828_, 0);
v_isSharedCheck_6005_ = !lean_is_exclusive(v___x_5828_);
if (v_isSharedCheck_6005_ == 0)
{
v___x_6000_ = v___x_5828_;
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
else
{
lean_inc(v_a_5998_);
lean_dec(v___x_5828_);
v___x_6000_ = lean_box(0);
v_isShared_6001_ = v_isSharedCheck_6005_;
goto v_resetjp_5999_;
}
v_resetjp_5999_:
{
lean_object* v___x_6003_; 
if (v_isShared_6001_ == 0)
{
v___x_6003_ = v___x_6000_;
goto v_reusejp_6002_;
}
else
{
lean_object* v_reuseFailAlloc_6004_; 
v_reuseFailAlloc_6004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_a_5998_);
v___x_6003_ = v_reuseFailAlloc_6004_;
goto v_reusejp_6002_;
}
v_reusejp_6002_:
{
return v___x_6003_;
}
}
}
}
}
}
else
{
lean_object* v_a_6021_; lean_object* v___x_6023_; uint8_t v_isShared_6024_; uint8_t v_isSharedCheck_6028_; 
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_6021_ = lean_ctor_get(v___x_5801_, 0);
v_isSharedCheck_6028_ = !lean_is_exclusive(v___x_5801_);
if (v_isSharedCheck_6028_ == 0)
{
v___x_6023_ = v___x_5801_;
v_isShared_6024_ = v_isSharedCheck_6028_;
goto v_resetjp_6022_;
}
else
{
lean_inc(v_a_6021_);
lean_dec(v___x_5801_);
v___x_6023_ = lean_box(0);
v_isShared_6024_ = v_isSharedCheck_6028_;
goto v_resetjp_6022_;
}
v_resetjp_6022_:
{
lean_object* v___x_6026_; 
if (v_isShared_6024_ == 0)
{
v___x_6026_ = v___x_6023_;
goto v_reusejp_6025_;
}
else
{
lean_object* v_reuseFailAlloc_6027_; 
v_reuseFailAlloc_6027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6027_, 0, v_a_6021_);
v___x_6026_ = v_reuseFailAlloc_6027_;
goto v_reusejp_6025_;
}
v_reusejp_6025_:
{
return v___x_6026_;
}
}
}
}
else
{
lean_object* v___x_6029_; lean_object* v___x_6031_; 
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v___x_6029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
if (v_isShared_5799_ == 0)
{
lean_ctor_set(v___x_5798_, 0, v___x_6029_);
v___x_6031_ = v___x_5798_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6032_; 
v_reuseFailAlloc_6032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6032_, 0, v___x_6029_);
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
else
{
lean_object* v_a_6034_; lean_object* v___x_6036_; uint8_t v_isShared_6037_; uint8_t v_isSharedCheck_6041_; 
lean_dec_ref(v_scope_5559_);
lean_dec(v_goal_5558_);
v_a_6034_ = lean_ctor_get(v___x_5795_, 0);
v_isSharedCheck_6041_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_6041_ == 0)
{
v___x_6036_ = v___x_5795_;
v_isShared_6037_ = v_isSharedCheck_6041_;
goto v_resetjp_6035_;
}
else
{
lean_inc(v_a_6034_);
lean_dec(v___x_5795_);
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
v___jp_5572_:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5575_, 0, v_scope_5573_);
lean_ctor_set(v___x_5575_, 1, v_gs_5574_);
v___x_5576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5575_);
return v___x_5576_;
}
v___jp_5577_:
{
lean_object* v___x_5579_; lean_object* v___x_5580_; lean_object* v___x_5581_; lean_object* v___x_5582_; 
v___x_5579_ = lean_box(0);
v___x_5580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5580_, 0, v_g_5578_);
lean_ctor_set(v___x_5580_, 1, v___x_5579_);
v___x_5581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5581_, 0, v_scope_5559_);
lean_ctor_set(v___x_5581_, 1, v___x_5580_);
v___x_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5582_, 0, v___x_5581_);
return v___x_5582_;
}
v___jp_5583_:
{
lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5585_, 0, v_scope_5559_);
lean_ctor_set(v___x_5585_, 1, v_gs_5584_);
v___x_5586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5585_);
return v___x_5586_;
}
v___jp_5587_:
{
lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; 
v___x_5590_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5590_, 0, v___y_5589_);
lean_ctor_set(v___x_5590_, 1, v___y_5588_);
v___x_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5591_, 0, v___x_5590_);
v___x_5592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5591_);
return v___x_5592_;
}
v___jp_5593_:
{
lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; 
v___x_5596_ = lean_box(0);
v___x_5597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5597_, 0, v_g_5595_);
lean_ctor_set(v___x_5597_, 1, v___x_5596_);
v___x_5598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5598_, 0, v___y_5594_);
lean_ctor_set(v___x_5598_, 1, v___x_5597_);
v___x_5599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
return v___x_5599_;
}
v___jp_5600_:
{
lean_object* v___x_5603_; lean_object* v___x_5604_; 
v___x_5603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5603_, 0, v___y_5601_);
lean_ctor_set(v___x_5603_, 1, v_gs_5602_);
v___x_5604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
return v___x_5604_;
}
v___jp_5605_:
{
lean_object* v___x_5609_; 
v___x_5609_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5608_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_object* v___x_5611_; uint8_t v_isShared_5612_; uint8_t v_isSharedCheck_5619_; 
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5619_ == 0)
{
lean_object* v_unused_5620_; 
v_unused_5620_ = lean_ctor_get(v___x_5609_, 0);
lean_dec(v_unused_5620_);
v___x_5611_ = v___x_5609_;
v_isShared_5612_ = v_isSharedCheck_5619_;
goto v_resetjp_5610_;
}
else
{
lean_dec(v___x_5609_);
v___x_5611_ = lean_box(0);
v_isShared_5612_ = v_isSharedCheck_5619_;
goto v_resetjp_5610_;
}
v_resetjp_5610_:
{
lean_object* v___x_5613_; lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5617_; 
v___x_5613_ = lean_box(0);
v___x_5614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5614_, 0, v_g_5607_);
lean_ctor_set(v___x_5614_, 1, v___x_5613_);
v___x_5615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5615_, 0, v___y_5606_);
lean_ctor_set(v___x_5615_, 1, v___x_5614_);
if (v_isShared_5612_ == 0)
{
lean_ctor_set(v___x_5611_, 0, v___x_5615_);
v___x_5617_ = v___x_5611_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_dec(v_g_5607_);
lean_dec_ref(v___y_5606_);
v_a_5621_ = lean_ctor_get(v___x_5609_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5609_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5609_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
v___jp_5629_:
{
lean_object* v___x_5643_; 
v___x_5643_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5639_);
if (lean_obj_tag(v___x_5643_) == 0)
{
lean_object* v___x_5644_; 
lean_dec_ref_known(v___x_5643_, 1);
lean_inc_ref(v___y_5630_);
v___x_5644_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applyFrame(v___y_5630_, v_goal_5558_, v___y_5640_, v___y_5635_, v___y_5639_, v___y_5634_, v___y_5636_, v___y_5637_, v___y_5641_, v___y_5631_, v___y_5642_, v___y_5633_, v___y_5632_, v___y_5638_);
if (lean_obj_tag(v___x_5644_) == 0)
{
lean_object* v_a_5645_; 
v_a_5645_ = lean_ctor_get(v___x_5644_, 0);
lean_inc(v_a_5645_);
lean_dec_ref_known(v___x_5644_, 1);
if (lean_obj_tag(v_a_5645_) == 0)
{
lean_object* v_scope_5646_; lean_object* v_subgoals_5647_; 
lean_dec_ref(v___y_5630_);
v_scope_5646_ = lean_ctor_get(v_a_5645_, 0);
lean_inc_ref(v_scope_5646_);
v_subgoals_5647_ = lean_ctor_get(v_a_5645_, 1);
lean_inc(v_subgoals_5647_);
lean_dec_ref_known(v_a_5645_, 2);
v_scope_5573_ = v_scope_5646_;
v_gs_5574_ = v_subgoals_5647_;
goto v___jp_5572_;
}
else
{
lean_object* v_goal_5648_; lean_object* v_info_5649_; lean_object* v___x_5650_; 
v_goal_5648_ = lean_ctor_get(v_a_5645_, 0);
lean_inc(v_goal_5648_);
v_info_5649_ = lean_ctor_get(v_a_5645_, 1);
lean_inc_ref(v_info_5649_);
lean_dec_ref_known(v_a_5645_, 2);
v___x_5650_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v___y_5630_, v_goal_5648_, v_info_5649_, v___y_5635_, v___y_5639_, v___y_5634_, v___y_5636_, v___y_5637_, v___y_5641_, v___y_5631_, v___y_5642_, v___y_5633_, v___y_5632_, v___y_5638_);
return v___x_5650_;
}
}
else
{
lean_object* v_a_5651_; lean_object* v___x_5653_; uint8_t v_isShared_5654_; uint8_t v_isSharedCheck_5658_; 
lean_dec_ref(v___y_5630_);
v_a_5651_ = lean_ctor_get(v___x_5644_, 0);
v_isSharedCheck_5658_ = !lean_is_exclusive(v___x_5644_);
if (v_isSharedCheck_5658_ == 0)
{
v___x_5653_ = v___x_5644_;
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
else
{
lean_inc(v_a_5651_);
lean_dec(v___x_5644_);
v___x_5653_ = lean_box(0);
v_isShared_5654_ = v_isSharedCheck_5658_;
goto v_resetjp_5652_;
}
v_resetjp_5652_:
{
lean_object* v___x_5656_; 
if (v_isShared_5654_ == 0)
{
v___x_5656_ = v___x_5653_;
goto v_reusejp_5655_;
}
else
{
lean_object* v_reuseFailAlloc_5657_; 
v_reuseFailAlloc_5657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5657_, 0, v_a_5651_);
v___x_5656_ = v_reuseFailAlloc_5657_;
goto v_reusejp_5655_;
}
v_reusejp_5655_:
{
return v___x_5656_;
}
}
}
}
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
lean_dec_ref(v___y_5640_);
lean_dec_ref(v___y_5630_);
lean_dec(v_goal_5558_);
v_a_5659_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5643_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5643_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
v___jp_5667_:
{
lean_object* v___x_5683_; lean_object* v___x_5684_; lean_object* v___x_5685_; 
lean_dec_ref(v___y_5671_);
lean_dec_ref(v___y_5668_);
v___x_5683_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v___y_5670_);
v___x_5684_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v___y_5670_);
lean_inc_ref(v___x_5684_);
lean_inc_ref(v___x_5683_);
v___x_5685_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v___x_5683_, v___x_5684_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5685_) == 0)
{
lean_object* v_a_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5786_; 
v_a_5686_ = lean_ctor_get(v___x_5685_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v___x_5685_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5688_ = v___x_5685_;
v_isShared_5689_ = v_isSharedCheck_5786_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_a_5686_);
lean_dec(v___x_5685_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5786_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
uint8_t v___x_5690_; 
v___x_5690_ = lean_unbox(v_a_5686_);
lean_dec(v_a_5686_);
if (v___x_5690_ == 0)
{
lean_object* v___x_5691_; 
lean_del_object(v___x_5688_);
lean_dec_ref(v___x_5683_);
lean_inc_ref(v___y_5670_);
lean_inc(v_goal_5558_);
v___x_5691_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpConsumeMData_x3f(v_goal_5558_, v___y_5670_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5691_) == 0)
{
lean_object* v_a_5692_; 
v_a_5692_ = lean_ctor_get(v___x_5691_, 0);
lean_inc(v_a_5692_);
lean_dec_ref_known(v___x_5691_, 1);
if (lean_obj_tag(v_a_5692_) == 1)
{
lean_object* v_val_5693_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec(v_goal_5558_);
v_val_5693_ = lean_ctor_get(v_a_5692_, 0);
lean_inc(v_val_5693_);
lean_dec_ref_known(v_a_5692_, 1);
v___y_5594_ = v___y_5669_;
v_g_5595_ = v_val_5693_;
goto v___jp_5593_;
}
else
{
lean_object* v___x_5694_; 
lean_dec(v_a_5692_);
lean_inc_ref(v___y_5670_);
lean_inc(v_goal_5558_);
v___x_5694_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_5558_, v___y_5670_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5694_) == 0)
{
lean_object* v_a_5695_; 
v_a_5695_ = lean_ctor_get(v___x_5694_, 0);
lean_inc(v_a_5695_);
lean_dec_ref_known(v___x_5694_, 1);
if (lean_obj_tag(v_a_5695_) == 1)
{
lean_object* v_val_5696_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec(v_goal_5558_);
v_val_5696_ = lean_ctor_get(v_a_5695_, 0);
lean_inc(v_val_5696_);
lean_dec_ref_known(v_a_5695_, 1);
v___y_5606_ = v___y_5669_;
v_g_5607_ = v_val_5696_;
v___y_5608_ = v___y_5673_;
goto v___jp_5605_;
}
else
{
lean_object* v___x_5697_; 
lean_dec(v_a_5695_);
lean_inc_ref(v___y_5670_);
lean_inc(v_goal_5558_);
v___x_5697_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_5558_, v___y_5670_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5697_) == 0)
{
lean_object* v_a_5698_; 
v_a_5698_ = lean_ctor_get(v___x_5697_, 0);
lean_inc(v_a_5698_);
lean_dec_ref_known(v___x_5697_, 1);
if (lean_obj_tag(v_a_5698_) == 1)
{
lean_object* v_val_5699_; lean_object* v___x_5700_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec(v_goal_5558_);
v_val_5699_ = lean_ctor_get(v_a_5698_, 0);
lean_inc(v_val_5699_);
lean_dec_ref_known(v_a_5698_, 1);
v___x_5700_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_5673_);
if (lean_obj_tag(v___x_5700_) == 0)
{
lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5708_; 
v_isSharedCheck_5708_ = !lean_is_exclusive(v___x_5700_);
if (v_isSharedCheck_5708_ == 0)
{
lean_object* v_unused_5709_; 
v_unused_5709_ = lean_ctor_get(v___x_5700_, 0);
lean_dec(v_unused_5709_);
v___x_5702_ = v___x_5700_;
v_isShared_5703_ = v_isSharedCheck_5708_;
goto v_resetjp_5701_;
}
else
{
lean_dec(v___x_5700_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5708_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
lean_object* v___x_5704_; lean_object* v___x_5706_; 
v___x_5704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5704_, 0, v___y_5669_);
lean_ctor_set(v___x_5704_, 1, v_val_5699_);
if (v_isShared_5703_ == 0)
{
lean_ctor_set(v___x_5702_, 0, v___x_5704_);
v___x_5706_ = v___x_5702_;
goto v_reusejp_5705_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v___x_5704_);
v___x_5706_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5705_;
}
v_reusejp_5705_:
{
return v___x_5706_;
}
}
}
else
{
lean_object* v_a_5710_; lean_object* v___x_5712_; uint8_t v_isShared_5713_; uint8_t v_isSharedCheck_5717_; 
lean_dec(v_val_5699_);
lean_dec_ref(v___y_5669_);
v_a_5710_ = lean_ctor_get(v___x_5700_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5700_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5712_ = v___x_5700_;
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
else
{
lean_inc(v_a_5710_);
lean_dec(v___x_5700_);
v___x_5712_ = lean_box(0);
v_isShared_5713_ = v_isSharedCheck_5717_;
goto v_resetjp_5711_;
}
v_resetjp_5711_:
{
lean_object* v___x_5715_; 
if (v_isShared_5713_ == 0)
{
v___x_5715_ = v___x_5712_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_a_5710_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
}
else
{
lean_object* v___x_5718_; 
lean_dec(v_a_5698_);
lean_inc_ref(v___y_5670_);
lean_inc(v_goal_5558_);
v___x_5718_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_5558_, v___y_5670_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5718_) == 0)
{
lean_object* v_a_5719_; 
v_a_5719_ = lean_ctor_get(v___x_5718_, 0);
lean_inc(v_a_5719_);
lean_dec_ref_known(v___x_5718_, 1);
if (lean_obj_tag(v_a_5719_) == 1)
{
lean_object* v_val_5720_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec(v_goal_5558_);
v_val_5720_ = lean_ctor_get(v_a_5719_, 0);
lean_inc(v_val_5720_);
lean_dec_ref_known(v_a_5719_, 1);
v___y_5606_ = v___y_5669_;
v_g_5607_ = v_val_5720_;
v___y_5608_ = v___y_5673_;
goto v___jp_5605_;
}
else
{
lean_object* v___x_5721_; 
lean_dec(v_a_5719_);
lean_inc_ref(v___y_5670_);
lean_inc(v_goal_5558_);
v___x_5721_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_5558_, v___y_5670_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
if (lean_obj_tag(v___x_5721_) == 0)
{
lean_object* v_a_5722_; 
v_a_5722_ = lean_ctor_get(v___x_5721_, 0);
lean_inc(v_a_5722_);
lean_dec_ref_known(v___x_5721_, 1);
if (lean_obj_tag(v_a_5722_) == 1)
{
lean_object* v_val_5723_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec(v_goal_5558_);
v_val_5723_ = lean_ctor_get(v_a_5722_, 0);
lean_inc(v_val_5723_);
lean_dec_ref_known(v_a_5722_, 1);
v___y_5606_ = v___y_5669_;
v_g_5607_ = v_val_5723_;
v___y_5608_ = v___y_5673_;
goto v___jp_5605_;
}
else
{
lean_object* v___x_5724_; uint8_t v___x_5725_; 
lean_dec(v_a_5722_);
v___x_5724_ = l_Lean_Expr_getAppFn(v___x_5684_);
v___x_5725_ = l_Lean_Expr_isConst(v___x_5724_);
if (v___x_5725_ == 0)
{
uint8_t v___x_5726_; 
v___x_5726_ = l_Lean_Expr_isFVar(v___x_5724_);
lean_dec_ref(v___x_5724_);
if (v___x_5726_ == 0)
{
lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v_a_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5740_; 
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v___x_5727_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v___x_5728_ = l_Lean_MessageData_ofExpr(v___x_5684_);
v___x_5729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5729_, 0, v___x_5727_);
lean_ctor_set(v___x_5729_, 1, v___x_5728_);
v___x_5730_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3);
v___x_5731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5731_, 0, v___x_5729_);
lean_ctor_set(v___x_5731_, 1, v___x_5730_);
v___x_5732_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_5731_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
v_isSharedCheck_5740_ = !lean_is_exclusive(v___x_5732_);
if (v_isSharedCheck_5740_ == 0)
{
v___x_5735_ = v___x_5732_;
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_a_5733_);
lean_dec(v___x_5732_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5740_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5738_; 
if (v_isShared_5736_ == 0)
{
v___x_5738_ = v___x_5735_;
goto v_reusejp_5737_;
}
else
{
lean_object* v_reuseFailAlloc_5739_; 
v_reuseFailAlloc_5739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5739_, 0, v_a_5733_);
v___x_5738_ = v_reuseFailAlloc_5739_;
goto v_reusejp_5737_;
}
v_reusejp_5737_:
{
return v___x_5738_;
}
}
}
else
{
lean_dec_ref(v___x_5684_);
v___y_5630_ = v___y_5669_;
v___y_5631_ = v___y_5678_;
v___y_5632_ = v___y_5681_;
v___y_5633_ = v___y_5680_;
v___y_5634_ = v___y_5674_;
v___y_5635_ = v___y_5672_;
v___y_5636_ = v___y_5675_;
v___y_5637_ = v___y_5676_;
v___y_5638_ = v___y_5682_;
v___y_5639_ = v___y_5673_;
v___y_5640_ = v___y_5670_;
v___y_5641_ = v___y_5677_;
v___y_5642_ = v___y_5679_;
goto v___jp_5629_;
}
}
else
{
lean_dec_ref(v___x_5724_);
lean_dec_ref(v___x_5684_);
v___y_5630_ = v___y_5669_;
v___y_5631_ = v___y_5678_;
v___y_5632_ = v___y_5681_;
v___y_5633_ = v___y_5680_;
v___y_5634_ = v___y_5674_;
v___y_5635_ = v___y_5672_;
v___y_5636_ = v___y_5675_;
v___y_5637_ = v___y_5676_;
v___y_5638_ = v___y_5682_;
v___y_5639_ = v___y_5673_;
v___y_5640_ = v___y_5670_;
v___y_5641_ = v___y_5677_;
v___y_5642_ = v___y_5679_;
goto v___jp_5629_;
}
}
}
else
{
lean_object* v_a_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5748_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v_a_5741_ = lean_ctor_get(v___x_5721_, 0);
v_isSharedCheck_5748_ = !lean_is_exclusive(v___x_5721_);
if (v_isSharedCheck_5748_ == 0)
{
v___x_5743_ = v___x_5721_;
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_a_5741_);
lean_dec(v___x_5721_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5748_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5746_; 
if (v_isShared_5744_ == 0)
{
v___x_5746_ = v___x_5743_;
goto v_reusejp_5745_;
}
else
{
lean_object* v_reuseFailAlloc_5747_; 
v_reuseFailAlloc_5747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5747_, 0, v_a_5741_);
v___x_5746_ = v_reuseFailAlloc_5747_;
goto v_reusejp_5745_;
}
v_reusejp_5745_:
{
return v___x_5746_;
}
}
}
}
}
else
{
lean_object* v_a_5749_; lean_object* v___x_5751_; uint8_t v_isShared_5752_; uint8_t v_isSharedCheck_5756_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v_a_5749_ = lean_ctor_get(v___x_5718_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5718_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5751_ = v___x_5718_;
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
else
{
lean_inc(v_a_5749_);
lean_dec(v___x_5718_);
v___x_5751_ = lean_box(0);
v_isShared_5752_ = v_isSharedCheck_5756_;
goto v_resetjp_5750_;
}
v_resetjp_5750_:
{
lean_object* v___x_5754_; 
if (v_isShared_5752_ == 0)
{
v___x_5754_ = v___x_5751_;
goto v_reusejp_5753_;
}
else
{
lean_object* v_reuseFailAlloc_5755_; 
v_reuseFailAlloc_5755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5755_, 0, v_a_5749_);
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
}
else
{
lean_object* v_a_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5764_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v_a_5757_ = lean_ctor_get(v___x_5697_, 0);
v_isSharedCheck_5764_ = !lean_is_exclusive(v___x_5697_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5759_ = v___x_5697_;
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_a_5757_);
lean_dec(v___x_5697_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5764_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5762_; 
if (v_isShared_5760_ == 0)
{
v___x_5762_ = v___x_5759_;
goto v_reusejp_5761_;
}
else
{
lean_object* v_reuseFailAlloc_5763_; 
v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
v___x_5762_ = v_reuseFailAlloc_5763_;
goto v_reusejp_5761_;
}
v_reusejp_5761_:
{
return v___x_5762_;
}
}
}
}
}
else
{
lean_object* v_a_5765_; lean_object* v___x_5767_; uint8_t v_isShared_5768_; uint8_t v_isSharedCheck_5772_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v_a_5765_ = lean_ctor_get(v___x_5694_, 0);
v_isSharedCheck_5772_ = !lean_is_exclusive(v___x_5694_);
if (v_isSharedCheck_5772_ == 0)
{
v___x_5767_ = v___x_5694_;
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
else
{
lean_inc(v_a_5765_);
lean_dec(v___x_5694_);
v___x_5767_ = lean_box(0);
v_isShared_5768_ = v_isSharedCheck_5772_;
goto v_resetjp_5766_;
}
v_resetjp_5766_:
{
lean_object* v___x_5770_; 
if (v_isShared_5768_ == 0)
{
v___x_5770_ = v___x_5767_;
goto v_reusejp_5769_;
}
else
{
lean_object* v_reuseFailAlloc_5771_; 
v_reuseFailAlloc_5771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5771_, 0, v_a_5765_);
v___x_5770_ = v_reuseFailAlloc_5771_;
goto v_reusejp_5769_;
}
v_reusejp_5769_:
{
return v___x_5770_;
}
}
}
}
}
else
{
lean_object* v_a_5773_; lean_object* v___x_5775_; uint8_t v_isShared_5776_; uint8_t v_isSharedCheck_5780_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v_a_5773_ = lean_ctor_get(v___x_5691_, 0);
v_isSharedCheck_5780_ = !lean_is_exclusive(v___x_5691_);
if (v_isSharedCheck_5780_ == 0)
{
v___x_5775_ = v___x_5691_;
v_isShared_5776_ = v_isSharedCheck_5780_;
goto v_resetjp_5774_;
}
else
{
lean_inc(v_a_5773_);
lean_dec(v___x_5691_);
v___x_5775_ = lean_box(0);
v_isShared_5776_ = v_isSharedCheck_5780_;
goto v_resetjp_5774_;
}
v_resetjp_5774_:
{
lean_object* v___x_5778_; 
if (v_isShared_5776_ == 0)
{
v___x_5778_ = v___x_5775_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_a_5773_);
v___x_5778_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
return v___x_5778_;
}
}
}
}
else
{
lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5784_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v___x_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5781_, 0, v___x_5683_);
v___x_5782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5782_, 0, v___x_5781_);
if (v_isShared_5689_ == 0)
{
lean_ctor_set(v___x_5688_, 0, v___x_5782_);
v___x_5784_ = v___x_5688_;
goto v_reusejp_5783_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v___x_5782_);
v___x_5784_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5783_;
}
v_reusejp_5783_:
{
return v___x_5784_;
}
}
}
}
else
{
lean_object* v_a_5787_; lean_object* v___x_5789_; uint8_t v_isShared_5790_; uint8_t v_isSharedCheck_5794_; 
lean_dec_ref(v___x_5684_);
lean_dec_ref(v___x_5683_);
lean_dec_ref(v___y_5670_);
lean_dec_ref(v___y_5669_);
lean_dec(v_goal_5558_);
v_a_5787_ = lean_ctor_get(v___x_5685_, 0);
v_isSharedCheck_5794_ = !lean_is_exclusive(v___x_5685_);
if (v_isSharedCheck_5794_ == 0)
{
v___x_5789_ = v___x_5685_;
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
else
{
lean_inc(v_a_5787_);
lean_dec(v___x_5685_);
v___x_5789_ = lean_box(0);
v_isShared_5790_ = v_isSharedCheck_5794_;
goto v_resetjp_5788_;
}
v_resetjp_5788_:
{
lean_object* v___x_5792_; 
if (v_isShared_5790_ == 0)
{
v___x_5792_ = v___x_5789_;
goto v_reusejp_5791_;
}
else
{
lean_object* v_reuseFailAlloc_5793_; 
v_reuseFailAlloc_5793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5793_, 0, v_a_5787_);
v___x_5792_ = v_reuseFailAlloc_5793_;
goto v_reusejp_5791_;
}
v_reusejp_5791_:
{
return v___x_5792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_6042_, lean_object* v_scope_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_, lean_object* v___y_6048_, lean_object* v___y_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_){
_start:
{
lean_object* v_res_6056_; 
v_res_6056_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_6042_, v_scope_6043_, v___y_6044_, v___y_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec(v___y_6052_);
lean_dec_ref(v___y_6051_);
lean_dec(v___y_6050_);
lean_dec_ref(v___y_6049_);
lean_dec(v___y_6048_);
lean_dec_ref(v___y_6047_);
lean_dec(v___y_6046_);
lean_dec(v___y_6045_);
lean_dec_ref(v___y_6044_);
return v_res_6056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_scope_6057_, lean_object* v_goal_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_){
_start:
{
lean_object* v___f_6071_; lean_object* v___x_6072_; 
lean_inc(v_goal_6058_);
v___f_6071_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_6071_, 0, v_goal_6058_);
lean_closure_set(v___f_6071_, 1, v_scope_6057_);
v___x_6072_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_6058_, v___f_6071_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_, v_a_6068_, v_a_6069_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_scope_6073_, lean_object* v_goal_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_, lean_object* v_a_6078_, lean_object* v_a_6079_, lean_object* v_a_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_){
_start:
{
lean_object* v_res_6087_; 
v_res_6087_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_6073_, v_goal_6074_, v_a_6075_, v_a_6076_, v_a_6077_, v_a_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
lean_dec(v_a_6085_);
lean_dec_ref(v_a_6084_);
lean_dec(v_a_6083_);
lean_dec_ref(v_a_6082_);
lean_dec(v_a_6081_);
lean_dec_ref(v_a_6080_);
lean_dec(v_a_6079_);
lean_dec_ref(v_a_6078_);
lean_dec(v_a_6077_);
lean_dec(v_a_6076_);
lean_dec_ref(v_a_6075_);
return v_res_6087_;
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
