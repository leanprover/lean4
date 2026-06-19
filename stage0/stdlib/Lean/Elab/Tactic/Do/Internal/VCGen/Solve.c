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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getUserName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_instantiateRevBetaS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Pattern_match_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_betaRevS___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsHygienic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_unfoldTriple(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 104, .m_capacity = 104, .m_length = 103, .m_data = "mvcgen': shared-continuation handling for `__do_jp` is not yet implemented. Detection point reached at "};
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
static const lean_string_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(147, 6, 42, 106, 0, 77, 75, 237)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Failed to apply "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__4;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " to"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__7;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fvar-zeta: "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
uint8_t v___y_712_; 
if (lean_obj_tag(v_x_708_) == 5)
{
lean_object* v_fn_721_; lean_object* v_arg_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v_fn_721_ = lean_ctor_get(v_x_708_, 0);
lean_inc_ref(v_fn_721_);
v_arg_722_ = lean_ctor_get(v_x_708_, 1);
lean_inc_ref(v_arg_722_);
lean_dec_ref_known(v_x_708_, 2);
v___x_723_ = lean_array_set(v_x_709_, v_x_710_, v_arg_722_);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_sub(v_x_710_, v___x_724_);
lean_dec(v_x_710_);
v_x_708_ = v_fn_721_;
v_x_709_ = v___x_723_;
v_x_710_ = v___x_725_;
goto _start;
}
else
{
lean_object* v___x_727_; uint8_t v___x_728_; 
lean_dec(v_x_710_);
v___x_727_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0___closed__1));
v___x_728_ = l_Lean_Expr_isConstOf(v_x_708_, v___x_727_);
if (v___x_728_ == 0)
{
v___y_712_ = v___x_728_;
goto v___jp_711_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(11u);
v___x_730_ = lean_array_get_size(v_x_709_);
v___x_731_ = lean_nat_dec_le(v___x_729_, v___x_730_);
v___y_712_ = v___x_731_;
goto v___jp_711_;
}
}
v___jp_711_:
{
if (v___y_712_ == 0)
{
lean_object* v___x_713_; 
lean_dec_ref(v_x_709_);
lean_dec_ref(v_x_708_);
v___x_713_ = lean_box(0);
return v___x_713_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_714_ = lean_unsigned_to_nat(11u);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_Array_extract___redArg(v_x_709_, v___x_715_, v___x_714_);
v___x_717_ = lean_array_get_size(v_x_709_);
v___x_718_ = l_Array_extract___redArg(v_x_709_, v___x_714_, v___x_717_);
lean_dec_ref(v_x_709_);
v___x_719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_719_, 0, v_x_708_);
lean_ctor_set(v___x_719_, 1, v___x_716_);
lean_ctor_set(v___x_719_, 2, v___x_718_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
return v___x_720_;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0(void){
_start:
{
lean_object* v___x_732_; lean_object* v_dummy_733_; 
v___x_732_ = lean_box(0);
v_dummy_733_ = l_Lean_Expr_sort___override(v___x_732_);
return v_dummy_733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(lean_object* v_rhs_734_){
_start:
{
lean_object* v_dummy_735_; lean_object* v_nargs_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_dummy_735_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_736_ = l_Lean_Expr_getAppNumArgs(v_rhs_734_);
lean_inc(v_nargs_736_);
v___x_737_ = lean_mk_array(v_nargs_736_, v_dummy_735_);
v___x_738_ = lean_unsigned_to_nat(1u);
v___x_739_ = lean_nat_sub(v_nargs_736_, v___x_738_);
lean_dec(v_nargs_736_);
v___x_740_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f_spec__0(v_rhs_734_, v___x_737_, v___x_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_741_, lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_x_744_){
_start:
{
lean_object* v_ks_745_; lean_object* v_vs_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_770_; 
v_ks_745_ = lean_ctor_get(v_x_741_, 0);
v_vs_746_ = lean_ctor_get(v_x_741_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_741_);
if (v_isSharedCheck_770_ == 0)
{
v___x_748_ = v_x_741_;
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_vs_746_);
lean_inc(v_ks_745_);
lean_dec(v_x_741_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_770_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = lean_array_get_size(v_ks_745_);
v___x_751_ = lean_nat_dec_lt(v_x_742_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
lean_dec(v_x_742_);
v___x_752_ = lean_array_push(v_ks_745_, v_x_743_);
v___x_753_ = lean_array_push(v_vs_746_, v_x_744_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_753_);
lean_ctor_set(v___x_748_, 0, v___x_752_);
v___x_755_ = v___x_748_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v___x_753_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
else
{
lean_object* v_k_x27_757_; uint8_t v___x_758_; 
v_k_x27_757_ = lean_array_fget_borrowed(v_ks_745_, v_x_742_);
v___x_758_ = l_Lean_instBEqMVarId_beq(v_x_743_, v_k_x27_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_760_; 
if (v_isShared_749_ == 0)
{
v___x_760_ = v___x_748_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_ks_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_vs_746_);
v___x_760_ = v_reuseFailAlloc_764_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_x_742_, v___x_761_);
lean_dec(v_x_742_);
v_x_741_ = v___x_760_;
v_x_742_ = v___x_762_;
goto _start;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_765_ = lean_array_fset(v_ks_745_, v_x_742_, v_x_743_);
v___x_766_ = lean_array_fset(v_vs_746_, v_x_742_, v_x_744_);
lean_dec(v_x_742_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_766_);
lean_ctor_set(v___x_748_, 0, v___x_765_);
v___x_768_ = v___x_748_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v___x_766_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_771_, lean_object* v_k_772_, lean_object* v_v_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_771_, v___x_774_, v_k_772_, v_v_773_);
return v___x_775_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_776_; size_t v___x_777_; size_t v___x_778_; 
v___x_776_ = ((size_t)5ULL);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_shift_left(v___x_777_, v___x_776_);
return v___x_778_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_779_; size_t v___x_780_; size_t v___x_781_; 
v___x_779_ = ((size_t)1ULL);
v___x_780_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_781_ = lean_usize_sub(v___x_780_, v___x_779_);
return v___x_781_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_782_; 
v___x_782_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_x_783_, size_t v_x_784_, size_t v_x_785_, lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
if (lean_obj_tag(v_x_783_) == 0)
{
lean_object* v_es_788_; size_t v___x_789_; size_t v___x_790_; size_t v___x_791_; size_t v___x_792_; lean_object* v_j_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_es_788_ = lean_ctor_get(v_x_783_, 0);
v___x_789_ = ((size_t)5ULL);
v___x_790_ = ((size_t)1ULL);
v___x_791_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_792_ = lean_usize_land(v_x_784_, v___x_791_);
v_j_793_ = lean_usize_to_nat(v___x_792_);
v___x_794_ = lean_array_get_size(v_es_788_);
v___x_795_ = lean_nat_dec_lt(v_j_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_dec(v_j_793_);
lean_dec(v_x_787_);
lean_dec(v_x_786_);
return v_x_783_;
}
else
{
lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_832_; 
lean_inc_ref(v_es_788_);
v_isSharedCheck_832_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_832_ == 0)
{
lean_object* v_unused_833_; 
v_unused_833_ = lean_ctor_get(v_x_783_, 0);
lean_dec(v_unused_833_);
v___x_797_ = v_x_783_;
v_isShared_798_ = v_isSharedCheck_832_;
goto v_resetjp_796_;
}
else
{
lean_dec(v_x_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_832_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v_v_799_; lean_object* v___x_800_; lean_object* v_xs_x27_801_; lean_object* v___y_803_; 
v_v_799_ = lean_array_fget(v_es_788_, v_j_793_);
v___x_800_ = lean_box(0);
v_xs_x27_801_ = lean_array_fset(v_es_788_, v_j_793_, v___x_800_);
switch(lean_obj_tag(v_v_799_))
{
case 0:
{
lean_object* v_key_808_; lean_object* v_val_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_819_; 
v_key_808_ = lean_ctor_get(v_v_799_, 0);
v_val_809_ = lean_ctor_get(v_v_799_, 1);
v_isSharedCheck_819_ = !lean_is_exclusive(v_v_799_);
if (v_isSharedCheck_819_ == 0)
{
v___x_811_ = v_v_799_;
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_val_809_);
lean_inc(v_key_808_);
lean_dec(v_v_799_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_819_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
uint8_t v___x_813_; 
v___x_813_ = l_Lean_instBEqMVarId_beq(v_x_786_, v_key_808_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_del_object(v___x_811_);
v___x_814_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_808_, v_val_809_, v_x_786_, v_x_787_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
v___y_803_ = v___x_815_;
goto v___jp_802_;
}
else
{
lean_object* v___x_817_; 
lean_dec(v_val_809_);
lean_dec(v_key_808_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 1, v_x_787_);
lean_ctor_set(v___x_811_, 0, v_x_786_);
v___x_817_ = v___x_811_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_x_786_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v_x_787_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
v___y_803_ = v___x_817_;
goto v___jp_802_;
}
}
}
}
case 1:
{
lean_object* v_node_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_830_; 
v_node_820_ = lean_ctor_get(v_v_799_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v_v_799_);
if (v_isSharedCheck_830_ == 0)
{
v___x_822_ = v_v_799_;
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_node_820_);
lean_dec(v_v_799_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_830_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
size_t v___x_824_; size_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_824_ = lean_usize_shift_right(v_x_784_, v___x_789_);
v___x_825_ = lean_usize_add(v_x_785_, v___x_790_);
v___x_826_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_node_820_, v___x_824_, v___x_825_, v_x_786_, v_x_787_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 0, v___x_826_);
v___x_828_ = v___x_822_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
v___y_803_ = v___x_828_;
goto v___jp_802_;
}
}
}
default: 
{
lean_object* v___x_831_; 
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v_x_786_);
lean_ctor_set(v___x_831_, 1, v_x_787_);
v___y_803_ = v___x_831_;
goto v___jp_802_;
}
}
v___jp_802_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_array_fset(v_xs_x27_801_, v_j_793_, v___y_803_);
lean_dec(v_j_793_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
else
{
lean_object* v_ks_834_; lean_object* v_vs_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_855_; 
v_ks_834_ = lean_ctor_get(v_x_783_, 0);
v_vs_835_ = lean_ctor_get(v_x_783_, 1);
v_isSharedCheck_855_ = !lean_is_exclusive(v_x_783_);
if (v_isSharedCheck_855_ == 0)
{
v___x_837_ = v_x_783_;
v_isShared_838_ = v_isSharedCheck_855_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_vs_835_);
lean_inc(v_ks_834_);
lean_dec(v_x_783_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_855_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v_ks_834_);
lean_ctor_set(v_reuseFailAlloc_854_, 1, v_vs_835_);
v___x_840_ = v_reuseFailAlloc_854_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v_newNode_841_; uint8_t v___y_843_; size_t v___x_849_; uint8_t v___x_850_; 
v_newNode_841_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v___x_840_, v_x_786_, v_x_787_);
v___x_849_ = ((size_t)7ULL);
v___x_850_ = lean_usize_dec_le(v___x_849_, v_x_785_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_851_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_841_);
v___x_852_ = lean_unsigned_to_nat(4u);
v___x_853_ = lean_nat_dec_lt(v___x_851_, v___x_852_);
lean_dec(v___x_851_);
v___y_843_ = v___x_853_;
goto v___jp_842_;
}
else
{
v___y_843_ = v___x_850_;
goto v___jp_842_;
}
v___jp_842_:
{
if (v___y_843_ == 0)
{
lean_object* v_ks_844_; lean_object* v_vs_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_ks_844_ = lean_ctor_get(v_newNode_841_, 0);
lean_inc_ref(v_ks_844_);
v_vs_845_ = lean_ctor_get(v_newNode_841_, 1);
lean_inc_ref(v_vs_845_);
lean_dec_ref(v_newNode_841_);
v___x_846_ = lean_unsigned_to_nat(0u);
v___x_847_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___closed__2);
v___x_848_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_x_785_, v_ks_844_, v_vs_845_, v___x_846_, v___x_847_);
lean_dec_ref(v_vs_845_);
lean_dec_ref(v_ks_844_);
return v___x_848_;
}
else
{
return v_newNode_841_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_856_, lean_object* v_keys_857_, lean_object* v_vals_858_, lean_object* v_i_859_, lean_object* v_entries_860_){
_start:
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_array_get_size(v_keys_857_);
v___x_862_ = lean_nat_dec_lt(v_i_859_, v___x_861_);
if (v___x_862_ == 0)
{
lean_dec(v_i_859_);
return v_entries_860_;
}
else
{
lean_object* v_k_863_; lean_object* v_v_864_; uint64_t v___x_865_; size_t v_h_866_; size_t v___x_867_; lean_object* v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; size_t v_h_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_k_863_ = lean_array_fget_borrowed(v_keys_857_, v_i_859_);
v_v_864_ = lean_array_fget_borrowed(v_vals_858_, v_i_859_);
v___x_865_ = l_Lean_instHashableMVarId_hash(v_k_863_);
v_h_866_ = lean_uint64_to_usize(v___x_865_);
v___x_867_ = ((size_t)5ULL);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_sub(v_depth_856_, v___x_869_);
v___x_871_ = lean_usize_mul(v___x_867_, v___x_870_);
v_h_872_ = lean_usize_shift_right(v_h_866_, v___x_871_);
v___x_873_ = lean_nat_add(v_i_859_, v___x_868_);
lean_dec(v_i_859_);
lean_inc(v_v_864_);
lean_inc(v_k_863_);
v___x_874_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_entries_860_, v_h_872_, v_depth_856_, v_k_863_, v_v_864_);
v_i_859_ = v___x_873_;
v_entries_860_ = v___x_874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_876_, lean_object* v_keys_877_, lean_object* v_vals_878_, lean_object* v_i_879_, lean_object* v_entries_880_){
_start:
{
size_t v_depth_boxed_881_; lean_object* v_res_882_; 
v_depth_boxed_881_ = lean_unbox_usize(v_depth_876_);
lean_dec(v_depth_876_);
v_res_882_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_881_, v_keys_877_, v_vals_878_, v_i_879_, v_entries_880_);
lean_dec_ref(v_vals_878_);
lean_dec_ref(v_keys_877_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_x_886_, lean_object* v_x_887_){
_start:
{
size_t v_x_8528__boxed_888_; size_t v_x_8529__boxed_889_; lean_object* v_res_890_; 
v_x_8528__boxed_888_ = lean_unbox_usize(v_x_884_);
lean_dec(v_x_884_);
v_x_8529__boxed_889_ = lean_unbox_usize(v_x_885_);
lean_dec(v_x_885_);
v_res_890_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_883_, v_x_8528__boxed_888_, v_x_8529__boxed_889_, v_x_886_, v_x_887_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_x_893_){
_start:
{
uint64_t v___x_894_; size_t v___x_895_; size_t v___x_896_; lean_object* v___x_897_; 
v___x_894_ = l_Lean_instHashableMVarId_hash(v_x_892_);
v___x_895_ = lean_uint64_to_usize(v___x_894_);
v___x_896_ = ((size_t)1ULL);
v___x_897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_891_, v___x_895_, v___x_896_, v_x_892_, v_x_893_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(lean_object* v_mvarId_898_, lean_object* v_val_899_, lean_object* v___y_900_){
_start:
{
lean_object* v___x_902_; lean_object* v_mctx_903_; lean_object* v_cache_904_; lean_object* v_zetaDeltaFVarIds_905_; lean_object* v_postponed_906_; lean_object* v_diag_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_935_; 
v___x_902_ = lean_st_ref_take(v___y_900_);
v_mctx_903_ = lean_ctor_get(v___x_902_, 0);
v_cache_904_ = lean_ctor_get(v___x_902_, 1);
v_zetaDeltaFVarIds_905_ = lean_ctor_get(v___x_902_, 2);
v_postponed_906_ = lean_ctor_get(v___x_902_, 3);
v_diag_907_ = lean_ctor_get(v___x_902_, 4);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_935_ == 0)
{
v___x_909_ = v___x_902_;
v_isShared_910_ = v_isSharedCheck_935_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_diag_907_);
lean_inc(v_postponed_906_);
lean_inc(v_zetaDeltaFVarIds_905_);
lean_inc(v_cache_904_);
lean_inc(v_mctx_903_);
lean_dec(v___x_902_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_935_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v_depth_911_; lean_object* v_levelAssignDepth_912_; lean_object* v_lmvarCounter_913_; lean_object* v_mvarCounter_914_; lean_object* v_lDecls_915_; lean_object* v_decls_916_; lean_object* v_userNames_917_; lean_object* v_lAssignment_918_; lean_object* v_eAssignment_919_; lean_object* v_dAssignment_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_934_; 
v_depth_911_ = lean_ctor_get(v_mctx_903_, 0);
v_levelAssignDepth_912_ = lean_ctor_get(v_mctx_903_, 1);
v_lmvarCounter_913_ = lean_ctor_get(v_mctx_903_, 2);
v_mvarCounter_914_ = lean_ctor_get(v_mctx_903_, 3);
v_lDecls_915_ = lean_ctor_get(v_mctx_903_, 4);
v_decls_916_ = lean_ctor_get(v_mctx_903_, 5);
v_userNames_917_ = lean_ctor_get(v_mctx_903_, 6);
v_lAssignment_918_ = lean_ctor_get(v_mctx_903_, 7);
v_eAssignment_919_ = lean_ctor_get(v_mctx_903_, 8);
v_dAssignment_920_ = lean_ctor_get(v_mctx_903_, 9);
v_isSharedCheck_934_ = !lean_is_exclusive(v_mctx_903_);
if (v_isSharedCheck_934_ == 0)
{
v___x_922_ = v_mctx_903_;
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_dAssignment_920_);
lean_inc(v_eAssignment_919_);
lean_inc(v_lAssignment_918_);
lean_inc(v_userNames_917_);
lean_inc(v_decls_916_);
lean_inc(v_lDecls_915_);
lean_inc(v_mvarCounter_914_);
lean_inc(v_lmvarCounter_913_);
lean_inc(v_levelAssignDepth_912_);
lean_inc(v_depth_911_);
lean_dec(v_mctx_903_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_934_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_eAssignment_919_, v_mvarId_898_, v_val_899_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 8, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_depth_911_);
lean_ctor_set(v_reuseFailAlloc_933_, 1, v_levelAssignDepth_912_);
lean_ctor_set(v_reuseFailAlloc_933_, 2, v_lmvarCounter_913_);
lean_ctor_set(v_reuseFailAlloc_933_, 3, v_mvarCounter_914_);
lean_ctor_set(v_reuseFailAlloc_933_, 4, v_lDecls_915_);
lean_ctor_set(v_reuseFailAlloc_933_, 5, v_decls_916_);
lean_ctor_set(v_reuseFailAlloc_933_, 6, v_userNames_917_);
lean_ctor_set(v_reuseFailAlloc_933_, 7, v_lAssignment_918_);
lean_ctor_set(v_reuseFailAlloc_933_, 8, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_933_, 9, v_dAssignment_920_);
v___x_926_ = v_reuseFailAlloc_933_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 0, v___x_926_);
v___x_928_ = v___x_909_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_926_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_cache_904_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v_zetaDeltaFVarIds_905_);
lean_ctor_set(v_reuseFailAlloc_932_, 3, v_postponed_906_);
lean_ctor_set(v_reuseFailAlloc_932_, 4, v_diag_907_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_929_ = lean_st_ref_set(v___y_900_, v___x_928_);
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_936_, lean_object* v_val_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_936_, v_val_937_, v___y_938_);
lean_dec(v___y_938_);
return v_res_940_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = l_Lean_Level_ofNat(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__4);
v___x_951_ = l_Lean_mkSort(v___x_950_);
return v___x_951_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__5);
v___x_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
return v___x_953_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_954_ = lean_box(0);
v___x_955_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__6);
v___x_956_ = lean_unsigned_to_nat(2u);
v___x_957_ = lean_mk_empty_array_with_capacity(v___x_956_);
v___x_958_ = lean_array_push(v___x_957_, v___x_955_);
v___x_959_ = lean_array_push(v___x_958_, v___x_954_);
return v___x_959_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_box(0);
v___x_973_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__12));
v___x_974_ = l_Lean_mkConst(v___x_973_, v___x_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(lean_object* v_goal_975_, lean_object* v_target_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v___x_989_; 
lean_inc_ref(v_target_976_);
v___x_989_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(v_target_976_);
if (lean_obj_tag(v___x_989_) == 1)
{
lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1056_; 
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1056_ == 0)
{
lean_object* v_unused_1057_; 
v_unused_1057_ = lean_ctor_get(v___x_989_, 0);
lean_dec(v_unused_1057_);
v___x_991_ = v___x_989_;
v_isShared_992_ = v_isSharedCheck_1056_;
goto v_resetjp_990_;
}
else
{
lean_dec(v___x_989_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1056_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_993_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_994_ = lean_unsigned_to_nat(2u);
v___x_995_ = lean_mk_empty_array_with_capacity(v___x_994_);
v___x_996_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__7);
v___x_997_ = l_Lean_Meta_mkAppOptM(v___x_993_, v___x_996_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
lean_inc(v_a_998_);
lean_dec_ref_known(v___x_997_, 1);
v___x_999_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_1000_ = lean_array_push(v___x_995_, v_a_998_);
lean_inc_ref(v_target_976_);
v___x_1001_ = lean_array_push(v___x_1000_, v_target_976_);
v___x_1002_ = l_Lean_Meta_mkAppM(v___x_999_, v___x_1001_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_1003_, v_a_983_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
v___x_1006_ = lean_box(0);
v___x_1007_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1005_, v___x_1006_, v_a_984_, v_a_985_, v_a_986_, v_a_987_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1022_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc_n(v_a_1008_, 2);
lean_dec_ref_known(v___x_1007_, 1);
v___x_1009_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__13);
v___x_1010_ = l_Lean_mkAppB(v___x_1009_, v_target_976_, v_a_1008_);
v___x_1011_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_975_, v___x_1010_, v_a_985_);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1023_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1022_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1022_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = l_Lean_Expr_mvarId_x21(v_a_1008_);
lean_dec(v_a_1008_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 0, v___x_1015_);
v___x_1017_ = v___x_991_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1019_; 
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1017_);
v___x_1019_ = v___x_1013_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_del_object(v___x_991_);
lean_dec_ref(v_target_976_);
lean_dec(v_goal_975_);
v_a_1024_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1007_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1007_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_del_object(v___x_991_);
lean_dec_ref(v_target_976_);
lean_dec(v_goal_975_);
v_a_1032_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1004_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1004_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_del_object(v___x_991_);
lean_dec_ref(v_target_976_);
lean_dec(v_goal_975_);
v_a_1040_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1002_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1002_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___x_995_);
lean_del_object(v___x_991_);
lean_dec_ref(v_target_976_);
lean_dec(v_goal_975_);
v_a_1048_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_997_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_997_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v___x_989_);
lean_dec_ref(v_target_976_);
lean_dec(v_goal_975_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___boxed(lean_object* v_goal_1060_, lean_object* v_target_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_1060_, v_target_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(lean_object* v_mvarId_1075_, lean_object* v_val_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_mvarId_1075_, v_val_1076_, v___y_1085_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___boxed(lean_object* v_mvarId_1090_, lean_object* v_val_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0(v_mvarId_1090_, v_val_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec_ref(v___y_1092_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0___redArg(v_x_1106_, v_x_1107_, v_x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1110_, lean_object* v_x_1111_, size_t v_x_1112_, size_t v_x_1113_, lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___redArg(v_x_1111_, v_x_1112_, v_x_1113_, v_x_1114_, v_x_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1117_, lean_object* v_x_1118_, lean_object* v_x_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
size_t v_x_9044__boxed_1123_; size_t v_x_9045__boxed_1124_; lean_object* v_res_1125_; 
v_x_9044__boxed_1123_ = lean_unbox_usize(v_x_1119_);
lean_dec(v_x_1119_);
v_x_9045__boxed_1124_ = lean_unbox_usize(v_x_1120_);
lean_dec(v_x_1120_);
v_res_1125_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1117_, v_x_1118_, v_x_9044__boxed_1123_, v_x_9045__boxed_1124_, v_x_1121_, v_x_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1126_, lean_object* v_n_1127_, lean_object* v_k_1128_, lean_object* v_v_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1127_, v_k_1128_, v_v_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_1131_, size_t v_depth_1132_, lean_object* v_keys_1133_, lean_object* v_vals_1134_, lean_object* v_heq_1135_, lean_object* v_i_1136_, lean_object* v_entries_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_1132_, v_keys_1133_, v_vals_1134_, v_i_1136_, v_entries_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_1139_, lean_object* v_depth_1140_, lean_object* v_keys_1141_, lean_object* v_vals_1142_, lean_object* v_heq_1143_, lean_object* v_i_1144_, lean_object* v_entries_1145_){
_start:
{
size_t v_depth_boxed_1146_; lean_object* v_res_1147_; 
v_depth_boxed_1146_ = lean_unbox_usize(v_depth_1140_);
lean_dec(v_depth_1140_);
v_res_1147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_1139_, v_depth_boxed_1146_, v_keys_1141_, v_vals_1142_, v_heq_1143_, v_i_1144_, v_entries_1145_);
lean_dec_ref(v_vals_1142_);
lean_dec_ref(v_keys_1141_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_, lean_object* v_x_1151_, lean_object* v_x_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_1149_, v_x_1150_, v_x_1151_, v_x_1152_);
return v___x_1153_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__0));
v___x_1156_ = l_Lean_stringToMessageData(v___x_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(lean_object* v_goal_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_){
_start:
{
lean_object* v_backwardRules_1166_; lean_object* v_refl_1167_; lean_object* v___x_1168_; 
v_backwardRules_1166_ = lean_ctor_get(v_a_1158_, 0);
v_refl_1167_ = lean_ctor_get(v_backwardRules_1166_, 7);
lean_inc_ref(v_refl_1167_);
lean_inc(v_goal_1157_);
v___x_1168_ = l_Lean_Meta_Sym_BackwardRule_apply(v_goal_1157_, v_refl_1167_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1207_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1207_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1207_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
if (lean_obj_tag(v_a_1169_) == 1)
{
lean_object* v_mvarIds_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1202_; 
v_mvarIds_1173_ = lean_ctor_get(v_a_1169_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_a_1169_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1175_ = v_a_1169_;
v_isShared_1176_ = v_isSharedCheck_1202_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_mvarIds_1173_);
lean_dec(v_a_1169_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1202_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_options_1184_; uint8_t v_hasTrace_1185_; 
v_options_1184_ = lean_ctor_get(v_a_1163_, 2);
v_hasTrace_1185_ = lean_ctor_get_uint8(v_options_1184_, sizeof(void*)*1);
if (v_hasTrace_1185_ == 0)
{
lean_dec(v_goal_1157_);
goto v___jp_1177_;
}
else
{
lean_object* v_inheritedTraceOptions_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_inheritedTraceOptions_1186_ = lean_ctor_get(v_a_1163_, 13);
v___x_1187_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1188_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1186_, v_options_1184_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_dec(v_goal_1157_);
goto v___jp_1177_;
}
else
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___closed__1);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_goal_1157_);
v___x_1192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1187_, v___x_1192_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_dec_ref_known(v___x_1193_, 1);
goto v___jp_1177_;
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_del_object(v___x_1175_);
lean_dec(v_mvarIds_1173_);
lean_del_object(v___x_1171_);
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1193_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1193_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
}
v___jp_1177_:
{
lean_object* v___x_1179_; 
if (v_isShared_1176_ == 0)
{
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_mvarIds_1173_);
v___x_1179_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
lean_object* v___x_1181_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1179_);
v___x_1181_ = v___x_1171_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
else
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_dec(v_a_1169_);
lean_dec(v_goal_1157_);
v___x_1203_ = lean_box(0);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1203_);
v___x_1205_ = v___x_1171_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
else
{
lean_object* v_a_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_goal_1157_);
v_a_1208_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1168_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_a_1208_);
lean_dec(v___x_1168_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg___boxed(lean_object* v_goal_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_, lean_object* v_a_1223_, lean_object* v_a_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_, v_a_1222_, v_a_1223_);
lean_dec(v_a_1223_);
lean_dec_ref(v_a_1222_);
lean_dec(v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec_ref(v_a_1218_);
lean_dec_ref(v_a_1217_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(lean_object* v_goal_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_, lean_object* v_a_1235_, lean_object* v_a_1236_, lean_object* v_a_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_1226_, v_a_1227_, v_a_1232_, v_a_1233_, v_a_1234_, v_a_1235_, v_a_1236_, v_a_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___boxed(lean_object* v_goal_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f(v_goal_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_);
lean_dec(v_a_1251_);
lean_dec_ref(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec_ref(v_a_1248_);
lean_dec(v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec_ref(v_a_1241_);
return v_res_1253_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1(void){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__0));
v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(lean_object* v_scope_1257_, lean_object* v_e_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_lastLiftedPre_x3f_1264_; 
v_lastLiftedPre_x3f_1264_ = lean_ctor_get(v_scope_1257_, 2);
lean_inc(v_lastLiftedPre_x3f_1264_);
lean_dec_ref(v_scope_1257_);
if (lean_obj_tag(v_lastLiftedPre_x3f_1264_) == 1)
{
lean_object* v_val_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1320_; 
v_val_1265_ = lean_ctor_get(v_lastLiftedPre_x3f_1264_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_lastLiftedPre_x3f_1264_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1267_ = v_lastLiftedPre_x3f_1264_;
v_isShared_1268_ = v_isSharedCheck_1320_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_val_1265_);
lean_dec(v_lastLiftedPre_x3f_1264_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1320_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v_lctx_1269_; lean_object* v___x_1270_; 
v_lctx_1269_ = lean_ctor_get(v_a_1259_, 2);
lean_inc_ref(v_lctx_1269_);
v___x_1270_ = lean_local_ctx_find(v_lctx_1269_, v_val_1265_);
if (lean_obj_tag(v___x_1270_) == 1)
{
lean_object* v_val_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_val_1271_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1271_);
v___x_1272_ = l_Lean_LocalDecl_type(v_val_1271_);
v___x_1273_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_1258_, v___x_1272_);
lean_dec_ref(v___x_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1281_; 
lean_dec(v_val_1271_);
lean_del_object(v___x_1267_);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1282_);
v___x_1275_ = v___x_1270_;
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
else
{
lean_dec(v___x_1270_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1281_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1277_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1277_);
v___x_1279_ = v___x_1275_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
else
{
lean_object* v_options_1283_; uint8_t v_hasTrace_1284_; 
v_options_1283_ = lean_ctor_get(v_a_1261_, 2);
v_hasTrace_1284_ = lean_ctor_get_uint8(v_options_1283_, sizeof(void*)*1);
if (v_hasTrace_1284_ == 0)
{
lean_object* v___x_1286_; 
lean_dec(v_val_1271_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1270_);
v___x_1286_ = v___x_1267_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v___x_1270_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
else
{
lean_object* v_inheritedTraceOptions_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; uint8_t v___x_1291_; 
v_inheritedTraceOptions_1288_ = lean_ctor_get(v_a_1261_, 13);
v___x_1289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_1290_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_1291_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1288_, v_options_1283_, v___x_1290_);
if (v___x_1291_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v_val_1271_);
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1270_);
v___x_1293_ = v___x_1267_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1270_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_del_object(v___x_1267_);
v___x_1295_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___closed__1);
v___x_1296_ = l_Lean_LocalDecl_userName(v_val_1271_);
lean_dec(v_val_1271_);
v___x_1297_ = l_Lean_MessageData_ofName(v___x_1296_);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1295_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_1289_, v___x_1298_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v___x_1299_, 0);
lean_dec(v_unused_1307_);
v___x_1301_ = v___x_1299_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_dec(v___x_1299_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1270_);
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1270_);
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
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref_known(v___x_1270_, 1);
v_a_1308_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1299_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1299_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
lean_dec(v___x_1270_);
v___x_1316_ = lean_box(0);
if (v_isShared_1268_ == 0)
{
lean_ctor_set_tag(v___x_1267_, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1316_);
v___x_1318_ = v___x_1267_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v___x_1316_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
else
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec(v_lastLiftedPre_x3f_1264_);
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg___boxed(lean_object* v_scope_1323_, lean_object* v_e_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1323_, v_e_1324_, v_a_1325_, v_a_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec_ref(v_e_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(lean_object* v_scope_1331_, lean_object* v_e_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1331_, v_e_1332_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___boxed(lean_object* v_scope_1346_, lean_object* v_e_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f(v_scope_1346_, v_e_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec_ref(v_a_1353_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec_ref(v_e_1347_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(lean_object* v_x_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc(v___y_1364_);
lean_inc(v___y_1363_);
lean_inc_ref(v___y_1362_);
v___x_1374_ = lean_apply_12(v_x_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, lean_box(0));
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed(lean_object* v_x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0(v_x_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(lean_object* v_mvarId_1389_, lean_object* v_x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; 
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
v___f_1403_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1403_, 0, v_x_1390_);
lean_closure_set(v___f_1403_, 1, v___y_1391_);
lean_closure_set(v___f_1403_, 2, v___y_1392_);
lean_closure_set(v___f_1403_, 3, v___y_1393_);
lean_closure_set(v___f_1403_, 4, v___y_1394_);
lean_closure_set(v___f_1403_, 5, v___y_1395_);
lean_closure_set(v___f_1403_, 6, v___y_1396_);
lean_closure_set(v___f_1403_, 7, v___y_1397_);
v___x_1404_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1389_, v___f_1403_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1404_) == 0)
{
return v___x_1404_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg___boxed(lean_object* v_mvarId_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1413_, v_x_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(lean_object* v_00_u03b1_1428_, lean_object* v_mvarId_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_mvarId_1429_, v_x_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_mvarId_1445_, lean_object* v_x_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0(v_00_u03b1_1444_, v_mvarId_1445_, v_x_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(uint8_t v___x_1465_, lean_object* v_scope_1466_, lean_object* v_rhs_1467_, lean_object* v_pre_1468_, lean_object* v_goal_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
if (v___x_1465_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
lean_dec(v_goal_1469_);
lean_dec_ref(v_pre_1468_);
lean_dec_ref(v_rhs_1467_);
lean_dec_ref(v_scope_1466_);
v___x_1482_ = lean_box(0);
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v___x_1482_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; 
v___x_1484_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1466_, v_rhs_1467_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1521_; 
v_a_1485_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1487_ = v___x_1484_;
v_isShared_1488_ = v_isSharedCheck_1521_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v___x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1521_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
if (lean_obj_tag(v_a_1485_) == 1)
{
lean_object* v_val_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
lean_del_object(v___x_1487_);
v_val_1489_ = lean_ctor_get(v_a_1485_, 0);
lean_inc(v_val_1489_);
lean_dec_ref_known(v_a_1485_, 1);
v___x_1490_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___closed__1));
v___x_1491_ = l_Lean_LocalDecl_toExpr(v_val_1489_);
v___x_1492_ = lean_unsigned_to_nat(3u);
v___x_1493_ = lean_mk_empty_array_with_capacity(v___x_1492_);
v___x_1494_ = lean_array_push(v___x_1493_, v_pre_1468_);
v___x_1495_ = lean_array_push(v___x_1494_, v_rhs_1467_);
v___x_1496_ = lean_array_push(v___x_1495_, v___x_1491_);
v___x_1497_ = l_Lean_Meta_mkAppM(v___x_1490_, v___x_1496_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
if (lean_obj_tag(v___x_1497_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1507_; 
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1499_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1469_, v_a_1498_, v___y_1478_);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___x_1499_, 0);
lean_dec(v_unused_1508_);
v___x_1501_ = v___x_1499_;
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
else
{
lean_dec(v___x_1499_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1507_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
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
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
lean_dec(v_goal_1469_);
v_a_1509_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1516_ == 0)
{
v___x_1511_ = v___x_1497_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1497_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1509_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
lean_dec(v_a_1485_);
lean_dec(v_goal_1469_);
lean_dec_ref(v_pre_1468_);
lean_dec_ref(v_rhs_1467_);
v___x_1517_ = lean_box(0);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v___x_1517_);
v___x_1519_ = v___x_1487_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
lean_dec(v_goal_1469_);
lean_dec_ref(v_pre_1468_);
lean_dec_ref(v_rhs_1467_);
v_a_1522_ = lean_ctor_get(v___x_1484_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1484_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1484_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1484_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed(lean_object** _args){
lean_object* v___x_1530_ = _args[0];
lean_object* v_scope_1531_ = _args[1];
lean_object* v_rhs_1532_ = _args[2];
lean_object* v_pre_1533_ = _args[3];
lean_object* v_goal_1534_ = _args[4];
lean_object* v___y_1535_ = _args[5];
lean_object* v___y_1536_ = _args[6];
lean_object* v___y_1537_ = _args[7];
lean_object* v___y_1538_ = _args[8];
lean_object* v___y_1539_ = _args[9];
lean_object* v___y_1540_ = _args[10];
lean_object* v___y_1541_ = _args[11];
lean_object* v___y_1542_ = _args[12];
lean_object* v___y_1543_ = _args[13];
lean_object* v___y_1544_ = _args[14];
lean_object* v___y_1545_ = _args[15];
lean_object* v___y_1546_ = _args[16];
_start:
{
uint8_t v___x_7757__boxed_1547_; lean_object* v_res_1548_; 
v___x_7757__boxed_1547_ = lean_unbox(v___x_1530_);
v_res_1548_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0(v___x_7757__boxed_1547_, v_scope_1531_, v_rhs_1532_, v_pre_1533_, v_goal_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec_ref(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec(v___y_1536_);
lean_dec_ref(v___y_1535_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(lean_object* v_scope_1549_, lean_object* v_goal_1550_, lean_object* v_00_u03b1_1551_, lean_object* v_pre_1552_, lean_object* v_rhs_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
uint8_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___y_1568_; lean_object* v___x_1569_; 
v___x_1566_ = l_Lean_Expr_isProp(v_00_u03b1_1551_);
v___x_1567_ = lean_box(v___x_1566_);
lean_inc(v_goal_1550_);
v___y_1568_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___lam__0___boxed), 17, 5);
lean_closure_set(v___y_1568_, 0, v___x_1567_);
lean_closure_set(v___y_1568_, 1, v_scope_1549_);
lean_closure_set(v___y_1568_, 2, v_rhs_1553_);
lean_closure_set(v___y_1568_, 3, v_pre_1552_);
lean_closure_set(v___y_1568_, 4, v_goal_1550_);
v___x_1569_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1550_, v___y_1568_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f___boxed(lean_object** _args){
lean_object* v_scope_1570_ = _args[0];
lean_object* v_goal_1571_ = _args[1];
lean_object* v_00_u03b1_1572_ = _args[2];
lean_object* v_pre_1573_ = _args[3];
lean_object* v_rhs_1574_ = _args[4];
lean_object* v_a_1575_ = _args[5];
lean_object* v_a_1576_ = _args[6];
lean_object* v_a_1577_ = _args[7];
lean_object* v_a_1578_ = _args[8];
lean_object* v_a_1579_ = _args[9];
lean_object* v_a_1580_ = _args[10];
lean_object* v_a_1581_ = _args[11];
lean_object* v_a_1582_ = _args[12];
lean_object* v_a_1583_ = _args[13];
lean_object* v_a_1584_ = _args[14];
lean_object* v_a_1585_ = _args[15];
lean_object* v_a_1586_ = _args[16];
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_scope_1570_, v_goal_1571_, v_00_u03b1_1572_, v_pre_1573_, v_rhs_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
lean_dec_ref(v_a_1582_);
lean_dec(v_a_1581_);
lean_dec_ref(v_a_1580_);
lean_dec(v_a_1579_);
lean_dec_ref(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec(v_a_1576_);
lean_dec_ref(v_a_1575_);
lean_dec_ref(v_00_u03b1_1572_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(lean_object* v_scope_1588_, lean_object* v_target_1589_, lean_object* v_goal_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedPreFor_x3f___redArg(v_scope_1588_, v_target_1589_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1624_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1624_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1624_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1624_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
if (lean_obj_tag(v_a_1604_) == 1)
{
lean_object* v_val_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1618_; 
lean_del_object(v___x_1606_);
v_val_1608_ = lean_ctor_get(v_a_1604_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v_a_1604_, 1);
v___x_1609_ = l_Lean_LocalDecl_toExpr(v_val_1608_);
v___x_1610_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f_spec__0___redArg(v_goal_1590_, v___x_1609_, v___y_1599_);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1618_ == 0)
{
lean_object* v_unused_1619_; 
v_unused_1619_ = lean_ctor_get(v___x_1610_, 0);
lean_dec(v_unused_1619_);
v___x_1612_ = v___x_1610_;
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
else
{
lean_dec(v___x_1610_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__3));
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1614_);
v___x_1616_ = v___x_1612_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_dec(v_a_1604_);
lean_dec(v_goal_1590_);
v___x_1620_ = lean_box(0);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1620_);
v___x_1622_ = v___x_1606_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
else
{
lean_object* v_a_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1632_; 
lean_dec(v_goal_1590_);
v_a_1625_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1632_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1627_ = v___x_1603_;
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_a_1625_);
lean_dec(v___x_1603_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1632_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1630_; 
if (v_isShared_1628_ == 0)
{
v___x_1630_ = v___x_1627_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_a_1625_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed(lean_object* v_scope_1633_, lean_object* v_target_1634_, lean_object* v_goal_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0(v_scope_1633_, v_target_1634_, v_goal_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v_target_1634_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(lean_object* v_scope_1649_, lean_object* v_goal_1650_, lean_object* v_target_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v___f_1664_; lean_object* v___x_1665_; 
lean_inc(v_goal_1650_);
v___f_1664_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___lam__0___boxed), 15, 3);
lean_closure_set(v___f_1664_, 0, v_scope_1649_);
lean_closure_set(v___f_1664_, 1, v_target_1651_);
lean_closure_set(v___f_1664_, 2, v_goal_1650_);
v___x_1665_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_1650_, v___f_1664_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f___boxed(lean_object* v_scope_1666_, lean_object* v_goal_1667_, lean_object* v_target_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_1666_, v_goal_1667_, v_target_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
return v_res_1681_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__2));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(lean_object* v_goal_1690_, lean_object* v_pre_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_){
_start:
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = l_Lean_Expr_cleanupAnnotations(v_pre_1691_);
v___x_1708_ = l_Lean_Expr_isApp(v___x_1707_);
if (v___x_1708_ == 0)
{
lean_dec_ref(v___x_1707_);
lean_dec(v_goal_1690_);
goto v___jp_1704_;
}
else
{
lean_object* v_arg_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_arg_1709_ = lean_ctor_get(v___x_1707_, 1);
lean_inc_ref(v_arg_1709_);
v___x_1710_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1707_);
v___x_1711_ = l_Lean_Expr_isApp(v___x_1710_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v___x_1710_);
lean_dec_ref(v_arg_1709_);
lean_dec(v_goal_1690_);
goto v___jp_1704_;
}
else
{
lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1710_);
v___x_1713_ = l_Lean_Expr_isApp(v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec_ref(v___x_1712_);
lean_dec_ref(v_arg_1709_);
lean_dec(v_goal_1690_);
goto v___jp_1704_;
}
else
{
lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1712_);
v___x_1715_ = l_Lean_Expr_isApp(v___x_1714_);
if (v___x_1715_ == 0)
{
lean_dec_ref(v___x_1714_);
lean_dec_ref(v_arg_1709_);
lean_dec(v_goal_1690_);
goto v___jp_1704_;
}
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v___x_1716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1714_);
v___x_1717_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__1));
v___x_1718_ = l_Lean_Expr_isConstOf(v___x_1716_, v___x_1717_);
lean_dec_ref(v___x_1716_);
if (v___x_1718_ == 0)
{
lean_dec_ref(v_arg_1709_);
lean_dec(v_goal_1690_);
goto v___jp_1704_;
}
else
{
lean_object* v___x_1719_; uint8_t v___x_1720_; 
v___x_1719_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1720_ = l_Lean_Expr_isAppOf(v_arg_1709_, v___x_1719_);
lean_dec_ref(v_arg_1709_);
if (v___x_1720_ == 0)
{
lean_object* v___x_1721_; lean_object* v___x_1722_; 
lean_dec(v_goal_1690_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
return v___x_1722_;
}
else
{
lean_object* v_backwardRules_1723_; lean_object* v_meetTop_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_backwardRules_1723_ = lean_ctor_get(v_a_1692_, 0);
v_meetTop_1724_ = lean_ctor_get(v_backwardRules_1723_, 8);
v___x_1725_ = lean_box(0);
lean_inc(v_goal_1690_);
lean_inc_ref(v_meetTop_1724_);
v___x_1726_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_meetTop_1724_, v_goal_1690_, v___x_1725_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1753_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1729_ = v___x_1726_;
v_isShared_1730_ = v_isSharedCheck_1753_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1726_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1753_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v___y_1735_; 
if (lean_obj_tag(v_a_1727_) == 1)
{
lean_object* v_mvarIds_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1752_; 
v_mvarIds_1740_ = lean_ctor_get(v_a_1727_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_a_1727_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1742_ = v_a_1727_;
v_isShared_1743_ = v_isSharedCheck_1752_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_mvarIds_1740_);
lean_dec(v_a_1727_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1752_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
if (lean_obj_tag(v_mvarIds_1740_) == 1)
{
lean_object* v_tail_1744_; 
v_tail_1744_ = lean_ctor_get(v_mvarIds_1740_, 1);
if (lean_obj_tag(v_tail_1744_) == 0)
{
lean_object* v_head_1745_; lean_object* v___x_1747_; 
lean_dec(v_goal_1690_);
v_head_1745_ = lean_ctor_get(v_mvarIds_1740_, 0);
lean_inc(v_head_1745_);
lean_dec_ref_known(v_mvarIds_1740_, 2);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 0, v_head_1745_);
v___x_1747_ = v___x_1742_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_head_1745_);
v___x_1747_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1747_);
v___x_1749_ = v___x_1729_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1740_, 2);
lean_del_object(v___x_1742_);
lean_del_object(v___x_1729_);
v___y_1732_ = v_a_1699_;
v___y_1733_ = v_a_1700_;
v___y_1734_ = v_a_1701_;
v___y_1735_ = v_a_1702_;
goto v___jp_1731_;
}
}
else
{
lean_del_object(v___x_1742_);
lean_dec(v_mvarIds_1740_);
lean_del_object(v___x_1729_);
v___y_1732_ = v_a_1699_;
v___y_1733_ = v_a_1700_;
v___y_1734_ = v_a_1701_;
v___y_1735_ = v_a_1702_;
goto v___jp_1731_;
}
}
}
else
{
lean_del_object(v___x_1729_);
lean_dec(v_a_1727_);
v___y_1732_ = v_a_1699_;
v___y_1733_ = v_a_1700_;
v___y_1734_ = v_a_1701_;
v___y_1735_ = v_a_1702_;
goto v___jp_1731_;
}
v___jp_1731_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1736_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___closed__3);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v_goal_1690_);
v___x_1738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1736_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
v___x_1739_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1738_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_);
return v___x_1739_;
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec(v_goal_1690_);
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
}
}
}
}
}
v___jp_1704_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f___boxed(lean_object* v_goal_1762_, lean_object* v_pre_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_1762_, v_pre_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_);
lean_dec(v_a_1774_);
lean_dec_ref(v_a_1773_);
lean_dec(v_a_1772_);
lean_dec_ref(v_a_1771_);
lean_dec(v_a_1770_);
lean_dec_ref(v_a_1769_);
lean_dec(v_a_1768_);
lean_dec_ref(v_a_1767_);
lean_dec(v_a_1766_);
lean_dec(v_a_1765_);
lean_dec_ref(v_a_1764_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(lean_object* v_goal_1784_, lean_object* v_pre_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = l_Lean_Expr_cleanupAnnotations(v_pre_1785_);
v___x_1802_ = l_Lean_Expr_isApp(v___x_1801_);
if (v___x_1802_ == 0)
{
lean_dec_ref(v___x_1801_);
lean_dec(v_goal_1784_);
goto v___jp_1798_;
}
else
{
lean_object* v_arg_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v_arg_1803_ = lean_ctor_get(v___x_1801_, 1);
lean_inc_ref(v_arg_1803_);
v___x_1804_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1801_);
v___x_1805_ = l_Lean_Expr_isApp(v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec_ref(v___x_1804_);
lean_dec_ref(v_arg_1803_);
lean_dec(v_goal_1784_);
goto v___jp_1798_;
}
else
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1804_);
v___x_1807_ = l_Lean_Expr_isApp(v___x_1806_);
if (v___x_1807_ == 0)
{
lean_dec_ref(v___x_1806_);
lean_dec_ref(v_arg_1803_);
lean_dec(v_goal_1784_);
goto v___jp_1798_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1808_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1806_);
v___x_1809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___closed__2));
v___x_1810_ = l_Lean_Expr_isConstOf(v___x_1808_, v___x_1809_);
lean_dec_ref(v___x_1808_);
if (v___x_1810_ == 0)
{
lean_dec_ref(v_arg_1803_);
lean_dec(v_goal_1784_);
goto v___jp_1798_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = l_Lean_Expr_isTrue(v_arg_1803_);
if (v___x_1811_ == 0)
{
lean_object* v_backwardRules_1812_; lean_object* v_ofPropPreIntro_1813_; lean_object* v___x_1814_; 
v_backwardRules_1812_ = lean_ctor_get(v_a_1786_, 0);
v_ofPropPreIntro_1813_ = lean_ctor_get(v_backwardRules_1812_, 3);
lean_inc_ref(v_ofPropPreIntro_1813_);
v___x_1814_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_ofPropPreIntro_1813_, v_goal_1784_, v_a_1786_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
v_a_1824_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1814_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1814_);
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
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec(v_goal_1784_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
}
}
v___jp_1798_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f___boxed(lean_object* v_goal_1834_, lean_object* v_pre_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_1834_, v_pre_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_, v_a_1845_, v_a_1846_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(lean_object* v_goal_1849_, lean_object* v_00_u03b1_1850_, lean_object* v_pre_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
uint8_t v___x_1864_; 
v___x_1864_ = l_Lean_Expr_isProp(v_00_u03b1_1850_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
lean_dec(v_goal_1849_);
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__3));
v___x_1868_ = l_Lean_Expr_isAppOf(v_pre_1851_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v_backwardRules_1869_; lean_object* v_propPreIntro_1870_; lean_object* v___x_1871_; 
v_backwardRules_1869_ = lean_ctor_get(v_a_1852_, 0);
v_propPreIntro_1870_ = lean_ctor_get(v_backwardRules_1869_, 2);
lean_inc_ref(v_propPreIntro_1870_);
v___x_1871_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introPre(v_propPreIntro_1870_, v_goal_1849_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_, v_a_1861_, v_a_1862_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1880_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1880_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1872_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 0, v___x_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
v_a_1881_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1871_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1871_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec(v_goal_1849_);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
return v___x_1890_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f___boxed(lean_object* v_goal_1891_, lean_object* v_00_u03b1_1892_, lean_object* v_pre_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_1891_, v_00_u03b1_1892_, v_pre_1893_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_, v_a_1903_, v_a_1904_);
lean_dec(v_a_1904_);
lean_dec_ref(v_a_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec_ref(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
lean_dec(v_a_1896_);
lean_dec(v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec_ref(v_pre_1893_);
lean_dec_ref(v_00_u03b1_1892_);
return v_res_1906_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__1(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__0));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__4(void){
_start:
{
uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = 0;
v___x_1916_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__3));
v___x_1917_ = l_Lean_MessageData_ofConstName(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__5(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__4);
v___x_1919_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__1);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1918_);
return v___x_1920_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__7(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__6));
v___x_1923_ = l_Lean_stringToMessageData(v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__8(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__7);
v___x_1925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__5);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
lean_ctor_set(v___x_1926_, 1, v___x_1924_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f(lean_object* v_goal_1927_, lean_object* v_pre_1928_, lean_object* v_target_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
uint8_t v___x_1942_; 
v___x_1942_ = l_Lean_Expr_isTrue(v_pre_1928_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec_ref(v_target_1929_);
lean_dec(v_goal_1927_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
else
{
lean_object* v_backwardRules_1945_; lean_object* v_truePreIntro_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_backwardRules_1945_ = lean_ctor_get(v_a_1930_, 0);
v_truePreIntro_1946_ = lean_ctor_get(v_backwardRules_1945_, 4);
v___x_1947_ = lean_box(0);
lean_inc_ref(v_truePreIntro_1946_);
v___x_1948_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_truePreIntro_1946_, v_goal_1927_, v___x_1947_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_, v_a_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1951_; uint8_t v_isShared_1952_; uint8_t v_isSharedCheck_1974_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1951_ = v___x_1948_;
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
else
{
lean_inc(v_a_1949_);
lean_dec(v___x_1948_);
v___x_1951_ = lean_box(0);
v_isShared_1952_ = v_isSharedCheck_1974_;
goto v_resetjp_1950_;
}
v_resetjp_1950_:
{
lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; 
if (lean_obj_tag(v_a_1949_) == 1)
{
lean_object* v_mvarIds_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1973_; 
v_mvarIds_1962_ = lean_ctor_get(v_a_1949_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_a_1949_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1964_ = v_a_1949_;
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_mvarIds_1962_);
lean_dec(v_a_1949_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
if (lean_obj_tag(v_mvarIds_1962_) == 1)
{
lean_object* v_tail_1966_; 
v_tail_1966_ = lean_ctor_get(v_mvarIds_1962_, 1);
if (lean_obj_tag(v_tail_1966_) == 0)
{
lean_object* v___x_1968_; 
lean_dec_ref(v_target_1929_);
if (v_isShared_1965_ == 0)
{
v___x_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_mvarIds_1962_);
v___x_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1970_; 
if (v_isShared_1952_ == 0)
{
lean_ctor_set(v___x_1951_, 0, v___x_1968_);
v___x_1970_ = v___x_1951_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_dec_ref_known(v_mvarIds_1962_, 2);
lean_del_object(v___x_1964_);
lean_del_object(v___x_1951_);
v___y_1954_ = v_a_1937_;
v___y_1955_ = v_a_1938_;
v___y_1956_ = v_a_1939_;
v___y_1957_ = v_a_1940_;
goto v___jp_1953_;
}
}
else
{
lean_del_object(v___x_1964_);
lean_dec(v_mvarIds_1962_);
lean_del_object(v___x_1951_);
v___y_1954_ = v_a_1937_;
v___y_1955_ = v_a_1938_;
v___y_1956_ = v_a_1939_;
v___y_1957_ = v_a_1940_;
goto v___jp_1953_;
}
}
}
else
{
lean_del_object(v___x_1951_);
lean_dec(v_a_1949_);
v___y_1954_ = v_a_1937_;
v___y_1955_ = v_a_1938_;
v___y_1956_ = v_a_1939_;
v___y_1957_ = v_a_1940_;
goto v___jp_1953_;
}
v___jp_1953_:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1958_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__8, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__8_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___closed__8);
v___x_1959_ = l_Lean_indentExpr(v_target_1929_);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_1960_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
return v___x_1961_;
}
}
}
else
{
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_target_1929_);
v_a_1975_ = lean_ctor_get(v___x_1948_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1948_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1948_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1948_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f___boxed(lean_object* v_goal_1983_, lean_object* v_pre_1984_, lean_object* v_target_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f(v_goal_1983_, v_pre_1984_, v_target_1985_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_, v_a_1996_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
lean_dec(v_a_1994_);
lean_dec_ref(v_a_1993_);
lean_dec(v_a_1992_);
lean_dec_ref(v_a_1991_);
lean_dec(v_a_1990_);
lean_dec_ref(v_a_1989_);
lean_dec(v_a_1988_);
lean_dec(v_a_1987_);
lean_dec_ref(v_a_1986_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(lean_object* v_scope_1999_, lean_object* v_goal_2000_, lean_object* v_00_u03b1_2001_, lean_object* v_pre_2002_, lean_object* v_target_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_g_2017_; lean_object* v_h_2018_; lean_object* v___x_2036_; 
lean_inc_ref(v_pre_2002_);
lean_inc(v_goal_2000_);
v___x_2036_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stripMeetTopPre_x3f(v_goal_2000_, v_pre_2002_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2137_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2039_ = v___x_2036_;
v_isShared_2040_ = v_isSharedCheck_2137_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_2036_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2137_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_object* v_val_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v_target_2003_);
lean_dec_ref(v_pre_2002_);
lean_dec(v_goal_2000_);
v_val_2041_ = lean_ctor_get(v_a_2037_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_a_2037_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2043_ = v_a_2037_;
v_isShared_2044_ = v_isSharedCheck_2054_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_val_2041_);
lean_dec(v_a_2037_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2054_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2045_ = lean_box(0);
v___x_2046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_val_2041_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v_scope_1999_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2047_);
v___x_2049_ = v___x_2043_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v___x_2049_);
v___x_2051_ = v___x_2039_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
}
}
}
}
else
{
lean_object* v___x_2055_; 
lean_del_object(v___x_2039_);
lean_dec(v_a_2037_);
lean_inc_ref(v_pre_2002_);
lean_inc(v_goal_2000_);
v___x_2055_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_ofPropPreIntro_x3f(v_goal_2000_, v_pre_2002_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
if (lean_obj_tag(v_a_2056_) == 1)
{
lean_object* v_val_2057_; lean_object* v_fst_2058_; lean_object* v_snd_2059_; 
lean_dec_ref(v_target_2003_);
lean_dec_ref(v_pre_2002_);
lean_dec(v_goal_2000_);
v_val_2057_ = lean_ctor_get(v_a_2056_, 0);
lean_inc(v_val_2057_);
lean_dec_ref_known(v_a_2056_, 1);
v_fst_2058_ = lean_ctor_get(v_val_2057_, 0);
lean_inc(v_fst_2058_);
v_snd_2059_ = lean_ctor_get(v_val_2057_, 1);
lean_inc(v_snd_2059_);
lean_dec(v_val_2057_);
v_g_2017_ = v_fst_2058_;
v_h_2018_ = v_snd_2059_;
goto v___jp_2016_;
}
else
{
uint8_t v___x_2060_; 
lean_dec(v_a_2056_);
v___x_2060_ = l_Lean_Expr_isForall(v_00_u03b1_2001_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_inc_ref(v_pre_2002_);
lean_inc(v_goal_2000_);
v___x_2061_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_truePre_x3f(v_goal_2000_, v_pre_2002_, v_target_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2099_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2064_ = v___x_2061_;
v_isShared_2065_ = v_isSharedCheck_2099_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_a_2062_);
lean_dec(v___x_2061_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2099_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
if (lean_obj_tag(v_a_2062_) == 1)
{
lean_object* v_val_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2077_; 
lean_dec_ref(v_pre_2002_);
lean_dec(v_goal_2000_);
v_val_2066_ = lean_ctor_get(v_a_2062_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_2062_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2068_ = v_a_2062_;
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_val_2066_);
lean_dec(v_a_2062_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v_scope_1999_);
lean_ctor_set(v___x_2070_, 1, v_val_2066_);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
lean_object* v___x_2074_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2072_);
v___x_2074_ = v___x_2064_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v___x_2072_);
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
lean_object* v___x_2078_; 
lean_del_object(v___x_2064_);
lean_dec(v_a_2062_);
v___x_2078_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_barePreIntro_x3f(v_goal_2000_, v_00_u03b1_2001_, v_pre_2002_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec_ref(v_pre_2002_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2090_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2081_ = v___x_2078_;
v_isShared_2082_ = v_isSharedCheck_2090_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2078_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2090_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
if (lean_obj_tag(v_a_2079_) == 1)
{
lean_object* v_val_2083_; lean_object* v_fst_2084_; lean_object* v_snd_2085_; 
lean_del_object(v___x_2081_);
v_val_2083_ = lean_ctor_get(v_a_2079_, 0);
lean_inc(v_val_2083_);
lean_dec_ref_known(v_a_2079_, 1);
v_fst_2084_ = lean_ctor_get(v_val_2083_, 0);
lean_inc(v_fst_2084_);
v_snd_2085_ = lean_ctor_get(v_val_2083_, 1);
lean_inc(v_snd_2085_);
lean_dec(v_val_2083_);
v_g_2017_ = v_fst_2084_;
v_h_2018_ = v_snd_2085_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2088_; 
lean_dec(v_a_2079_);
lean_dec_ref(v_scope_1999_);
v___x_2086_ = lean_box(0);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2086_);
v___x_2088_ = v___x_2081_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_scope_1999_);
v_a_2091_ = lean_ctor_get(v___x_2078_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2078_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2078_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2078_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_pre_2002_);
lean_dec(v_goal_2000_);
lean_dec_ref(v_scope_1999_);
v_a_2100_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2061_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2061_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v___x_2108_; 
lean_dec_ref(v_target_2003_);
lean_dec_ref(v_pre_2002_);
v___x_2108_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsExcessArgs(v_goal_2000_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2120_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2111_ = v___x_2108_;
v_isShared_2112_ = v_isSharedCheck_2120_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2108_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2120_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2114_, 0, v_a_2109_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_scope_1999_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2116_);
v___x_2118_ = v___x_2111_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v_scope_1999_);
v_a_2121_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2108_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2108_);
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
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v_target_2003_);
lean_dec_ref(v_pre_2002_);
lean_dec(v_goal_2000_);
lean_dec_ref(v_scope_1999_);
v_a_2129_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2055_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2055_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v_target_2003_);
lean_dec_ref(v_pre_2002_);
lean_dec(v_goal_2000_);
lean_dec_ref(v_scope_1999_);
v_a_2138_ = lean_ctor_get(v___x_2036_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2036_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2036_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2036_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
v___jp_2016_:
{
lean_object* v_specs_2019_; lean_object* v_jps_2020_; lean_object* v_nextDeclIdx_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2034_; 
v_specs_2019_ = lean_ctor_get(v_scope_1999_, 0);
v_jps_2020_ = lean_ctor_get(v_scope_1999_, 1);
v_nextDeclIdx_2021_ = lean_ctor_get(v_scope_1999_, 3);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_scope_1999_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_scope_1999_, 2);
lean_dec(v_unused_2035_);
v___x_2023_ = v_scope_1999_;
v_isShared_2024_ = v_isSharedCheck_2034_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_nextDeclIdx_2021_);
lean_inc(v_jps_2020_);
lean_inc(v_specs_2019_);
lean_dec(v_scope_1999_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2034_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_h_2018_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 2, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_specs_2019_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_jps_2020_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v_nextDeclIdx_2021_);
v___x_2027_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_g_2017_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
return v___x_2032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f___boxed(lean_object** _args){
lean_object* v_scope_2146_ = _args[0];
lean_object* v_goal_2147_ = _args[1];
lean_object* v_00_u03b1_2148_ = _args[2];
lean_object* v_pre_2149_ = _args[3];
lean_object* v_target_2150_ = _args[4];
lean_object* v_a_2151_ = _args[5];
lean_object* v_a_2152_ = _args[6];
lean_object* v_a_2153_ = _args[7];
lean_object* v_a_2154_ = _args[8];
lean_object* v_a_2155_ = _args[9];
lean_object* v_a_2156_ = _args[10];
lean_object* v_a_2157_ = _args[11];
lean_object* v_a_2158_ = _args[12];
lean_object* v_a_2159_ = _args[13];
lean_object* v_a_2160_ = _args[14];
lean_object* v_a_2161_ = _args[15];
lean_object* v_a_2162_ = _args[16];
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_2146_, v_goal_2147_, v_00_u03b1_2148_, v_pre_2149_, v_target_2150_, v_a_2151_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_, v_a_2157_, v_a_2158_, v_a_2159_, v_a_2160_, v_a_2161_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
lean_dec(v_a_2159_);
lean_dec_ref(v_a_2158_);
lean_dec(v_a_2157_);
lean_dec_ref(v_a_2156_);
lean_dec(v_a_2155_);
lean_dec_ref(v_a_2154_);
lean_dec(v_a_2153_);
lean_dec(v_a_2152_);
lean_dec_ref(v_a_2151_);
lean_dec_ref(v_00_u03b1_2148_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2164_, lean_object* v_a_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___y_2174_; lean_object* v___x_2177_; uint8_t v_debug_2178_; 
v___x_2177_ = lean_st_ref_get(v___y_2167_);
v_debug_2178_ = lean_ctor_get_uint8(v___x_2177_, sizeof(void*)*10);
lean_dec(v___x_2177_);
if (v_debug_2178_ == 0)
{
v___y_2174_ = v___y_2167_;
goto v___jp_2173_;
}
else
{
lean_object* v___x_2179_; 
lean_inc_ref(v_f_2164_);
v___x_2179_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2164_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v___x_2180_; 
lean_dec_ref_known(v___x_2179_, 1);
lean_inc_ref(v_a_2165_);
v___x_2180_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2165_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_dec_ref_known(v___x_2180_, 1);
v___y_2174_ = v___y_2167_;
goto v___jp_2173_;
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_f_2164_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_f_2164_);
v_a_2189_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2179_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2179_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
v___jp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2175_ = l_Lean_Expr_app___override(v_f_2164_, v_a_2165_);
v___x_2176_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2175_, v___y_2174_);
return v___x_2176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2197_, lean_object* v_a_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2197_, v_a_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(lean_object* v_args_2207_, lean_object* v_endIdx_2208_, lean_object* v_b_2209_, lean_object* v_i_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_nat_dec_le(v_endIdx_2208_, v_i_2210_);
if (v___x_2223_ == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2224_ = l_Lean_instInhabitedExpr;
v___x_2225_ = lean_array_get_borrowed(v___x_2224_, v_args_2207_, v_i_2210_);
lean_inc(v___x_2225_);
v___x_2226_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2209_, v___x_2225_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
if (lean_obj_tag(v___x_2226_) == 0)
{
lean_object* v_a_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v_a_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc(v_a_2227_);
lean_dec_ref_known(v___x_2226_, 1);
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_add(v_i_2210_, v___x_2228_);
lean_dec(v_i_2210_);
v_b_2209_ = v_a_2227_;
v_i_2210_ = v___x_2229_;
goto _start;
}
else
{
lean_dec(v_i_2210_);
return v___x_2226_;
}
}
else
{
lean_object* v___x_2231_; 
lean_dec(v_i_2210_);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v_b_2209_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0___boxed(lean_object* v_args_2232_, lean_object* v_endIdx_2233_, lean_object* v_b_2234_, lean_object* v_i_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_res_2248_; 
v_res_2248_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2232_, v_endIdx_2233_, v_b_2234_, v_i_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
lean_dec(v___y_2244_);
lean_dec_ref(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v_endIdx_2233_);
lean_dec_ref(v_args_2232_);
return v_res_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(lean_object* v_f_2249_, lean_object* v_args_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2263_ = lean_unsigned_to_nat(0u);
v___x_2264_ = lean_array_get_size(v_args_2250_);
v___x_2265_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0(v_args_2250_, v___x_2264_, v_f_2249_, v___x_2263_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0___boxed(lean_object* v_f_2266_, lean_object* v_args_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v_res_2280_; 
v_res_2280_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_f_2266_, v_args_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec_ref(v_args_2267_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(lean_object* v_goal_2281_, lean_object* v_target_2282_, lean_object* v_info_2283_, lean_object* v_prog_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_head_2297_; lean_object* v_args_2298_; lean_object* v_excessArgs_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v_head_2297_ = lean_ctor_get(v_info_2283_, 0);
lean_inc_ref(v_head_2297_);
v_args_2298_ = lean_ctor_get(v_info_2283_, 1);
lean_inc_ref(v_args_2298_);
v_excessArgs_2299_ = lean_ctor_get(v_info_2283_, 2);
lean_inc_ref(v_excessArgs_2299_);
lean_dec_ref(v_info_2283_);
v___x_2300_ = lean_unsigned_to_nat(8u);
v___x_2301_ = lean_array_set(v_args_2298_, v___x_2300_, v_prog_2284_);
v___x_2302_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2297_, v___x_2301_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec_ref(v___x_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
v___x_2304_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2303_, v_excessArgs_2299_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec_ref(v_excessArgs_2299_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; lean_object* v_dummy_2306_; lean_object* v_nargs_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2304_, 1);
v_dummy_2306_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_2307_ = l_Lean_Expr_getAppNumArgs(v_target_2282_);
lean_inc(v_nargs_2307_);
v___x_2308_ = lean_mk_array(v_nargs_2307_, v_dummy_2306_);
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_nat_sub(v_nargs_2307_, v___x_2309_);
lean_dec(v_nargs_2307_);
lean_inc_ref(v_target_2282_);
v___x_2311_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_2282_, v___x_2308_, v___x_2310_);
v___x_2312_ = l_Lean_Expr_getAppFn(v_target_2282_);
lean_dec_ref(v_target_2282_);
v___x_2313_ = lean_array_get_size(v___x_2311_);
v___x_2314_ = lean_nat_sub(v___x_2313_, v___x_2309_);
v___x_2315_ = lean_array_set(v___x_2311_, v___x_2314_, v_a_2305_);
lean_dec(v___x_2314_);
v___x_2316_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2312_, v___x_2315_, v_a_2285_, v_a_2286_, v_a_2287_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
lean_dec_ref(v___x_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_2281_, v_a_2317_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2318_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_goal_2281_);
v_a_2319_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2316_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2316_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v_target_2282_);
lean_dec(v_goal_2281_);
v_a_2327_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2304_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2304_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec_ref(v_excessArgs_2299_);
lean_dec_ref(v_target_2282_);
lean_dec(v_goal_2281_);
v_a_2335_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2302_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2302_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq___boxed(lean_object* v_goal_2343_, lean_object* v_target_2344_, lean_object* v_info_2345_, lean_object* v_prog_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2343_, v_target_2344_, v_info_2345_, v_prog_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
lean_dec(v_a_2357_);
lean_dec_ref(v_a_2356_);
lean_dec(v_a_2355_);
lean_dec_ref(v_a_2354_);
lean_dec(v_a_2353_);
lean_dec_ref(v_a_2352_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(lean_object* v_f_2360_, lean_object* v_a_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_f_2360_, v_a_2361_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___boxed(lean_object* v_f_2375_, lean_object* v_a_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1(v_f_2375_, v_a_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v___y_2381_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(lean_object* v_revArgs_2390_, lean_object* v_start_2391_, lean_object* v_b_2392_, lean_object* v_i_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
uint8_t v___x_2401_; 
v___x_2401_ = lean_nat_dec_le(v_i_2393_, v_start_2391_);
if (v___x_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v_i_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2402_ = lean_unsigned_to_nat(1u);
v_i_2403_ = lean_nat_sub(v_i_2393_, v___x_2402_);
lean_dec(v_i_2393_);
v___x_2404_ = l_Lean_instInhabitedExpr;
v___x_2405_ = lean_array_get_borrowed(v___x_2404_, v_revArgs_2390_, v_i_2403_);
lean_inc(v___x_2405_);
v___x_2406_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0_spec__0_spec__1___redArg(v_b_2392_, v___x_2405_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v_b_2392_ = v_a_2407_;
v_i_2393_ = v_i_2403_;
goto _start;
}
else
{
lean_dec(v_i_2403_);
return v___x_2406_;
}
}
else
{
lean_object* v___x_2409_; 
lean_dec(v_i_2393_);
v___x_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2409_, 0, v_b_2392_);
return v___x_2409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_revArgs_2410_, lean_object* v_start_2411_, lean_object* v_b_2412_, lean_object* v_i_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2410_, v_start_2411_, v_b_2412_, v_i_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v_start_2411_);
lean_dec_ref(v_revArgs_2410_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(lean_object* v_f_2422_, lean_object* v_revArgs_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2436_ = lean_unsigned_to_nat(0u);
v___x_2437_ = lean_array_get_size(v_revArgs_2423_);
v___x_2438_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2423_, v___x_2436_, v_f_2422_, v___x_2437_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0___boxed(lean_object* v_f_2439_, lean_object* v_revArgs_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_f_2439_, v_revArgs_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec_ref(v_revArgs_2440_);
return v_res_2453_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__0));
v___x_2456_ = l_Lean_stringToMessageData(v___x_2455_);
return v___x_2456_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__2));
v___x_2459_ = l_Lean_stringToMessageData(v___x_2458_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(lean_object* v_goal_2460_, lean_object* v_target_2461_, lean_object* v_info_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_){
_start:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2462_);
v___x_2476_ = l_Lean_Expr_getAppFn(v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 8)
{
lean_object* v_declName_2477_; lean_object* v_type_2478_; lean_object* v_value_2479_; lean_object* v_body_2480_; uint8_t v_nondep_2481_; lean_object* v___x_2482_; 
v_declName_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc_n(v_declName_2477_, 2);
v_type_2478_ = lean_ctor_get(v___x_2476_, 1);
lean_inc_ref(v_type_2478_);
v_value_2479_ = lean_ctor_get(v___x_2476_, 2);
lean_inc_ref(v_value_2479_);
v_body_2480_ = lean_ctor_get(v___x_2476_, 3);
lean_inc_ref(v_body_2480_);
v_nondep_2481_ = lean_ctor_get_uint8(v___x_2476_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v___x_2476_, 4);
v___x_2482_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_throwIfUnsupportedJP___redArg(v_declName_2477_, v_value_2479_, v_a_2463_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_appArgs_2485_; lean_object* v___y_2487_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2540_; lean_object* v___y_2541_; lean_object* v___y_2542_; lean_object* v___y_2543_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; uint8_t v___x_2639_; 
lean_dec_ref_known(v___x_2482_, 1);
v___x_2483_ = l_Lean_Expr_getAppNumArgs(v___x_2475_);
v___x_2484_ = lean_mk_empty_array_with_capacity(v___x_2483_);
lean_dec(v___x_2483_);
v_appArgs_2485_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_2475_, v___x_2484_);
v___x_2639_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_isDuplicable(v_value_2479_);
if (v___x_2639_ == 0)
{
lean_object* v_options_2640_; uint8_t v_hasTrace_2641_; 
v_options_2640_ = lean_ctor_get(v_a_2472_, 2);
v_hasTrace_2641_ = lean_ctor_get_uint8(v_options_2640_, sizeof(void*)*1);
if (v_hasTrace_2641_ == 0)
{
v___y_2540_ = v_a_2463_;
v___y_2541_ = v_a_2464_;
v___y_2542_ = v_a_2465_;
v___y_2543_ = v_a_2466_;
v___y_2544_ = v_a_2467_;
v___y_2545_ = v_a_2468_;
v___y_2546_ = v_a_2469_;
v___y_2547_ = v_a_2470_;
v___y_2548_ = v_a_2471_;
v___y_2549_ = v_a_2472_;
v___y_2550_ = v_a_2473_;
goto v___jp_2539_;
}
else
{
lean_object* v_inheritedTraceOptions_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; uint8_t v___x_2645_; 
v_inheritedTraceOptions_2642_ = lean_ctor_get(v_a_2472_, 13);
v___x_2643_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2644_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2642_, v_options_2640_, v___x_2644_);
if (v___x_2645_ == 0)
{
v___y_2540_ = v_a_2463_;
v___y_2541_ = v_a_2464_;
v___y_2542_ = v_a_2465_;
v___y_2543_ = v_a_2466_;
v___y_2544_ = v_a_2467_;
v___y_2545_ = v_a_2468_;
v___y_2546_ = v_a_2469_;
v___y_2547_ = v_a_2470_;
v___y_2548_ = v_a_2471_;
v___y_2549_ = v_a_2472_;
v___y_2550_ = v_a_2473_;
goto v___jp_2539_;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2646_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__3);
lean_inc(v_declName_2477_);
v___x_2647_ = l_Lean_MessageData_ofName(v_declName_2477_);
v___x_2648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2643_, v___x_2648_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_dec_ref_known(v___x_2649_, 1);
v___y_2540_ = v_a_2463_;
v___y_2541_ = v_a_2464_;
v___y_2542_ = v_a_2465_;
v___y_2543_ = v_a_2466_;
v___y_2544_ = v_a_2467_;
v___y_2545_ = v_a_2468_;
v___y_2546_ = v_a_2469_;
v___y_2547_ = v_a_2470_;
v___y_2548_ = v_a_2471_;
v___y_2549_ = v_a_2472_;
v___y_2550_ = v_a_2473_;
goto v___jp_2539_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v_appArgs_2485_);
lean_dec_ref(v_body_2480_);
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2649_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2649_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2649_);
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
}
}
else
{
lean_object* v_options_2658_; uint8_t v_hasTrace_2659_; 
lean_dec_ref(v_type_2478_);
v_options_2658_ = lean_ctor_get(v_a_2472_, 2);
v_hasTrace_2659_ = lean_ctor_get_uint8(v_options_2658_, sizeof(void*)*1);
if (v_hasTrace_2659_ == 0)
{
lean_dec(v_declName_2477_);
v___y_2487_ = v_a_2463_;
v___y_2488_ = v_a_2464_;
v___y_2489_ = v_a_2465_;
v___y_2490_ = v_a_2466_;
v___y_2491_ = v_a_2467_;
v___y_2492_ = v_a_2468_;
v___y_2493_ = v_a_2469_;
v___y_2494_ = v_a_2470_;
v___y_2495_ = v_a_2471_;
v___y_2496_ = v_a_2472_;
v___y_2497_ = v_a_2473_;
goto v___jp_2486_;
}
else
{
lean_object* v_inheritedTraceOptions_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
v_inheritedTraceOptions_2660_ = lean_ctor_get(v_a_2472_, 13);
v___x_2661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_2662_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_2663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2660_, v_options_2658_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_dec(v_declName_2477_);
v___y_2487_ = v_a_2463_;
v___y_2488_ = v_a_2464_;
v___y_2489_ = v_a_2465_;
v___y_2490_ = v_a_2466_;
v___y_2491_ = v_a_2467_;
v___y_2492_ = v_a_2468_;
v___y_2493_ = v_a_2469_;
v___y_2494_ = v_a_2470_;
v___y_2495_ = v_a_2471_;
v___y_2496_ = v_a_2472_;
v___y_2497_ = v_a_2473_;
goto v___jp_2486_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2664_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__11);
v___x_2665_ = l_Lean_MessageData_ofName(v_declName_2477_);
v___x_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2664_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_2661_, v___x_2666_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_dec_ref_known(v___x_2667_, 1);
v___y_2487_ = v_a_2463_;
v___y_2488_ = v_a_2464_;
v___y_2489_ = v_a_2465_;
v___y_2490_ = v_a_2466_;
v___y_2491_ = v_a_2467_;
v___y_2492_ = v_a_2468_;
v___y_2493_ = v_a_2469_;
v___y_2494_ = v_a_2470_;
v___y_2495_ = v_a_2471_;
v___y_2496_ = v_a_2472_;
v___y_2497_ = v_a_2473_;
goto v___jp_2486_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v_appArgs_2485_);
lean_dec_ref(v_body_2480_);
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2667_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2667_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
}
v___jp_2486_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2498_ = lean_unsigned_to_nat(1u);
v___x_2499_ = lean_mk_empty_array_with_capacity(v___x_2498_);
v___x_2500_ = lean_array_push(v___x_2499_, v_value_2479_);
v___x_2501_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(v_body_2480_, v___x_2500_, v___y_2493_);
lean_dec_ref(v___x_2500_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; lean_object* v___x_2503_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref_known(v___x_2501_, 1);
v___x_2503_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_a_2502_, v_appArgs_2485_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec_ref(v_appArgs_2485_);
if (lean_obj_tag(v___x_2503_) == 0)
{
lean_object* v_a_2504_; lean_object* v___x_2505_; 
v_a_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_a_2504_);
lean_dec_ref_known(v___x_2503_, 1);
v___x_2505_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2460_, v_target_2461_, v_info_2462_, v_a_2504_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2514_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2508_ = v___x_2505_;
v_isShared_2509_ = v_isSharedCheck_2514_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2505_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2514_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2506_);
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 0, v___x_2510_);
v___x_2512_ = v___x_2508_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
v_a_2515_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2505_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2505_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2523_ = lean_ctor_get(v___x_2503_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2503_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2503_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2503_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_appArgs_2485_);
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2531_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2501_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2501_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
v___jp_2539_:
{
lean_object* v___x_2551_; 
v___x_2551_ = l_Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0(v_body_2480_, v_appArgs_2485_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v_appArgs_2485_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v_head_2553_; lean_object* v_args_2554_; lean_object* v_excessArgs_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v_head_2553_ = lean_ctor_get(v_info_2462_, 0);
lean_inc_ref(v_head_2553_);
v_args_2554_ = lean_ctor_get(v_info_2462_, 1);
lean_inc_ref(v_args_2554_);
v_excessArgs_2555_ = lean_ctor_get(v_info_2462_, 2);
lean_inc_ref(v_excessArgs_2555_);
lean_dec_ref(v_info_2462_);
v___x_2556_ = lean_unsigned_to_nat(8u);
v___x_2557_ = lean_array_set(v_args_2554_, v___x_2556_, v_a_2552_);
v___x_2558_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_head_2553_, v___x_2557_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v___x_2557_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v_a_2559_; lean_object* v___x_2560_; 
v_a_2559_ = lean_ctor_get(v___x_2558_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___x_2558_, 1);
v___x_2560_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v_a_2559_, v_excessArgs_2555_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v_excessArgs_2555_);
if (lean_obj_tag(v___x_2560_) == 0)
{
lean_object* v_a_2561_; lean_object* v_dummy_2562_; lean_object* v_nargs_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_a_2561_ = lean_ctor_get(v___x_2560_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v___x_2560_, 1);
v_dummy_2562_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f___closed__0);
v_nargs_2563_ = l_Lean_Expr_getAppNumArgs(v_target_2461_);
lean_inc(v_nargs_2563_);
v___x_2564_ = lean_mk_array(v_nargs_2563_, v_dummy_2562_);
v___x_2565_ = lean_unsigned_to_nat(1u);
v___x_2566_ = lean_nat_sub(v_nargs_2563_, v___x_2565_);
lean_dec(v_nargs_2563_);
lean_inc_ref(v_target_2461_);
v___x_2567_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_target_2461_, v___x_2564_, v___x_2566_);
v___x_2568_ = l_Lean_Expr_getAppFn(v_target_2461_);
lean_dec_ref(v_target_2461_);
v___x_2569_ = lean_array_get_size(v___x_2567_);
v___x_2570_ = lean_nat_sub(v___x_2569_, v___x_2565_);
v___x_2571_ = lean_array_set(v___x_2567_, v___x_2570_, v_a_2561_);
lean_dec(v___x_2570_);
v___x_2572_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq_spec__0(v___x_2568_, v___x_2571_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec_ref(v___x_2571_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v___x_2574_ = l_Lean_Expr_letE___override(v_declName_2477_, v_type_2478_, v_value_2479_, v_a_2573_, v_nondep_2481_);
v___x_2575_ = l_Lean_MVarId_replaceTargetDefEq(v_goal_2460_, v___x_2574_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2578_ = l_Lean_Meta_Sym_intros(v_a_2576_, v___x_2577_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2590_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2590_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2590_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
if (lean_obj_tag(v_a_2579_) == 1)
{
lean_object* v_mvarId_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v_mvarId_2583_ = lean_ctor_get(v_a_2579_, 1);
lean_inc(v_mvarId_2583_);
lean_dec_ref_known(v_a_2579_, 2);
v___x_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2584_, 0, v_mvarId_2583_);
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 0, v___x_2584_);
v___x_2586_ = v___x_2581_;
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
else
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_del_object(v___x_2581_);
lean_dec(v_a_2579_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___closed__1);
v___x_2589_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2588_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
return v___x_2589_;
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
v_a_2591_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2578_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2578_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
else
{
lean_object* v_a_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2606_; 
v_a_2599_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2601_ = v___x_2575_;
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_a_2599_);
lean_dec(v___x_2575_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2606_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2604_; 
if (v_isShared_2602_ == 0)
{
v___x_2604_ = v___x_2601_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_a_2599_);
v___x_2604_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
return v___x_2604_;
}
}
}
}
else
{
lean_object* v_a_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2614_; 
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_declName_2477_);
lean_dec(v_goal_2460_);
v_a_2607_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2609_ = v___x_2572_;
v_isShared_2610_ = v_isSharedCheck_2614_;
goto v_resetjp_2608_;
}
else
{
lean_inc(v_a_2607_);
lean_dec(v___x_2572_);
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
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2615_ = lean_ctor_get(v___x_2560_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2560_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2560_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2560_);
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
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v_excessArgs_2555_);
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2623_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2558_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2558_);
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
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_declName_2477_);
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2631_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2551_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2551_);
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
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v_body_2480_);
lean_dec_ref(v_value_2479_);
lean_dec_ref(v_type_2478_);
lean_dec(v_declName_2477_);
lean_dec_ref(v___x_2475_);
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v_a_2676_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2482_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2482_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
else
{
lean_object* v___x_2684_; lean_object* v___x_2685_; 
lean_dec_ref(v___x_2476_);
lean_dec_ref(v___x_2475_);
lean_dec_ref(v_info_2462_);
lean_dec_ref(v_target_2461_);
lean_dec(v_goal_2460_);
v___x_2684_ = lean_box(0);
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f___boxed(lean_object* v_goal_2686_, lean_object* v_target_2687_, lean_object* v_info_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_2686_, v_target_2687_, v_info_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
lean_dec(v_a_2699_);
lean_dec_ref(v_a_2698_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
lean_dec(v_a_2693_);
lean_dec_ref(v_a_2692_);
lean_dec(v_a_2691_);
lean_dec(v_a_2690_);
lean_dec_ref(v_a_2689_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(lean_object* v_revArgs_2702_, lean_object* v_start_2703_, lean_object* v_b_2704_, lean_object* v_i_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___redArg(v_revArgs_2702_, v_start_2703_, v_b_2704_, v_i_2705_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0___boxed(lean_object* v_revArgs_2719_, lean_object* v_start_2720_, lean_object* v_b_2721_, lean_object* v_i_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppRevS___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f_spec__0_spec__0(v_revArgs_2719_, v_start_2720_, v_b_2721_, v_i_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v_start_2720_);
lean_dec_ref(v_revArgs_2719_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(lean_object* v_as_x27_2736_, lean_object* v_b_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
if (lean_obj_tag(v_as_x27_2736_) == 0)
{
lean_object* v___x_2747_; 
v___x_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_b_2737_);
return v___x_2747_;
}
else
{
lean_object* v_head_2748_; lean_object* v_tail_2749_; lean_object* v___x_2750_; 
v_head_2748_ = lean_ctor_get(v_as_x27_2736_, 0);
v_tail_2749_ = lean_ctor_get(v_as_x27_2736_, 1);
lean_inc(v_head_2748_);
v___x_2750_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpGoalTelescope___redArg(v_head_2748_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
switch(lean_obj_tag(v_a_2751_))
{
case 0:
{
lean_object* v___x_2752_; 
lean_inc(v_head_2748_);
v___x_2752_ = lean_array_push(v_b_2737_, v_head_2748_);
v_as_x27_2736_ = v_tail_2749_;
v_b_2737_ = v___x_2752_;
goto _start;
}
case 1:
{
v_as_x27_2736_ = v_tail_2749_;
goto _start;
}
default: 
{
lean_object* v_mvarId_2755_; lean_object* v___x_2756_; 
v_mvarId_2755_ = lean_ctor_get(v_a_2751_, 0);
lean_inc(v_mvarId_2755_);
lean_dec_ref_known(v_a_2751_, 1);
v___x_2756_ = lean_array_push(v_b_2737_, v_mvarId_2755_);
v_as_x27_2736_ = v_tail_2749_;
v_b_2737_ = v___x_2756_;
goto _start;
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_dec_ref(v_b_2737_);
v_a_2758_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2750_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2750_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg___boxed(lean_object* v_as_x27_2766_, lean_object* v_b_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_2766_, v_b_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v_as_x27_2766_);
return v_res_2777_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__0));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__2));
v___x_2783_ = l_Lean_stringToMessageData(v___x_2782_);
return v___x_2783_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4(void){
_start:
{
uint8_t v___x_2784_; uint64_t v___x_2785_; 
v___x_2784_ = 2;
v___x_2785_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(lean_object* v_goal_2786_, lean_object* v_target_2787_, lean_object* v_info_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_, lean_object* v_a_2795_, lean_object* v_a_2796_, lean_object* v_a_2797_, lean_object* v_a_2798_, lean_object* v_a_2799_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_2788_);
lean_inc_ref(v___x_2801_);
v___x_2802_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v___x_2801_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2976_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2976_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2976_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
if (lean_obj_tag(v_a_2803_) == 1)
{
lean_object* v_val_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2971_; 
lean_del_object(v___x_2805_);
v_val_2807_ = lean_ctor_get(v_a_2803_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_a_2803_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2809_ = v_a_2803_;
v_isShared_2810_ = v_isSharedCheck_2971_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_val_2807_);
lean_dec(v_a_2803_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2971_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2822_; 
if (lean_obj_tag(v_val_2807_) == 2)
{
lean_object* v___x_2879_; uint8_t v_foApprox_2880_; uint8_t v_ctxApprox_2881_; uint8_t v_quasiPatternApprox_2882_; uint8_t v_constApprox_2883_; uint8_t v_isDefEqStuckEx_2884_; uint8_t v_unificationHints_2885_; uint8_t v_proofIrrelevance_2886_; uint8_t v_assignSyntheticOpaque_2887_; uint8_t v_offsetCnstrs_2888_; uint8_t v_etaStruct_2889_; uint8_t v_univApprox_2890_; uint8_t v_iota_2891_; uint8_t v_beta_2892_; uint8_t v_proj_2893_; uint8_t v_zeta_2894_; uint8_t v_zetaDelta_2895_; uint8_t v_zetaUnused_2896_; uint8_t v_zetaHave_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2970_; 
v___x_2879_ = l_Lean_Meta_Context_config(v_a_2796_);
v_foApprox_2880_ = lean_ctor_get_uint8(v___x_2879_, 0);
v_ctxApprox_2881_ = lean_ctor_get_uint8(v___x_2879_, 1);
v_quasiPatternApprox_2882_ = lean_ctor_get_uint8(v___x_2879_, 2);
v_constApprox_2883_ = lean_ctor_get_uint8(v___x_2879_, 3);
v_isDefEqStuckEx_2884_ = lean_ctor_get_uint8(v___x_2879_, 4);
v_unificationHints_2885_ = lean_ctor_get_uint8(v___x_2879_, 5);
v_proofIrrelevance_2886_ = lean_ctor_get_uint8(v___x_2879_, 6);
v_assignSyntheticOpaque_2887_ = lean_ctor_get_uint8(v___x_2879_, 7);
v_offsetCnstrs_2888_ = lean_ctor_get_uint8(v___x_2879_, 8);
v_etaStruct_2889_ = lean_ctor_get_uint8(v___x_2879_, 10);
v_univApprox_2890_ = lean_ctor_get_uint8(v___x_2879_, 11);
v_iota_2891_ = lean_ctor_get_uint8(v___x_2879_, 12);
v_beta_2892_ = lean_ctor_get_uint8(v___x_2879_, 13);
v_proj_2893_ = lean_ctor_get_uint8(v___x_2879_, 14);
v_zeta_2894_ = lean_ctor_get_uint8(v___x_2879_, 15);
v_zetaDelta_2895_ = lean_ctor_get_uint8(v___x_2879_, 16);
v_zetaUnused_2896_ = lean_ctor_get_uint8(v___x_2879_, 17);
v_zetaHave_2897_ = lean_ctor_get_uint8(v___x_2879_, 18);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2899_ = v___x_2879_;
v_isShared_2900_ = v_isSharedCheck_2970_;
goto v_resetjp_2898_;
}
else
{
lean_dec(v___x_2879_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2970_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
uint8_t v_trackZetaDelta_2901_; lean_object* v_zetaDeltaSet_2902_; lean_object* v_lctx_2903_; lean_object* v_localInstances_2904_; lean_object* v_defEqCtx_x3f_2905_; lean_object* v_synthPendingDepth_2906_; lean_object* v_canUnfold_x3f_2907_; uint8_t v_univApprox_2908_; uint8_t v_inTypeClassResolution_2909_; uint8_t v_cacheInferType_2910_; uint8_t v___x_2911_; lean_object* v_config_2913_; 
v_trackZetaDelta_2901_ = lean_ctor_get_uint8(v_a_2796_, sizeof(void*)*7);
v_zetaDeltaSet_2902_ = lean_ctor_get(v_a_2796_, 1);
v_lctx_2903_ = lean_ctor_get(v_a_2796_, 2);
v_localInstances_2904_ = lean_ctor_get(v_a_2796_, 3);
v_defEqCtx_x3f_2905_ = lean_ctor_get(v_a_2796_, 4);
v_synthPendingDepth_2906_ = lean_ctor_get(v_a_2796_, 5);
v_canUnfold_x3f_2907_ = lean_ctor_get(v_a_2796_, 6);
v_univApprox_2908_ = lean_ctor_get_uint8(v_a_2796_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2909_ = lean_ctor_get_uint8(v_a_2796_, sizeof(void*)*7 + 2);
v_cacheInferType_2910_ = lean_ctor_get_uint8(v_a_2796_, sizeof(void*)*7 + 3);
v___x_2911_ = 2;
if (v_isShared_2900_ == 0)
{
v_config_2913_ = v___x_2899_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 0, v_foApprox_2880_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 1, v_ctxApprox_2881_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 2, v_quasiPatternApprox_2882_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 3, v_constApprox_2883_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 4, v_isDefEqStuckEx_2884_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 5, v_unificationHints_2885_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 6, v_proofIrrelevance_2886_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 7, v_assignSyntheticOpaque_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 8, v_offsetCnstrs_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 10, v_etaStruct_2889_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 11, v_univApprox_2890_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 12, v_iota_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 13, v_beta_2892_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 14, v_proj_2893_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 15, v_zeta_2894_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 16, v_zetaDelta_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 17, v_zetaUnused_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2969_, 18, v_zetaHave_2897_);
v_config_2913_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
uint64_t v___x_2914_; uint64_t v___x_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; uint64_t v_key_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
lean_ctor_set_uint8(v_config_2913_, 9, v___x_2911_);
v___x_2914_ = l_Lean_Meta_Context_configKey(v_a_2796_);
v___x_2915_ = 3ULL;
v___x_2916_ = lean_uint64_shift_right(v___x_2914_, v___x_2915_);
v___x_2917_ = lean_uint64_shift_left(v___x_2916_, v___x_2915_);
v___x_2918_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__4);
v_key_2919_ = lean_uint64_lor(v___x_2917_, v___x_2918_);
v___x_2920_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2920_, 0, v_config_2913_);
lean_ctor_set_uint64(v___x_2920_, sizeof(void*)*1, v_key_2919_);
lean_inc(v_canUnfold_x3f_2907_);
lean_inc(v_synthPendingDepth_2906_);
lean_inc(v_defEqCtx_x3f_2905_);
lean_inc_ref(v_localInstances_2904_);
lean_inc_ref(v_lctx_2903_);
lean_inc(v_zetaDeltaSet_2902_);
v___x_2921_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v_zetaDeltaSet_2902_);
lean_ctor_set(v___x_2921_, 2, v_lctx_2903_);
lean_ctor_set(v___x_2921_, 3, v_localInstances_2904_);
lean_ctor_set(v___x_2921_, 4, v_defEqCtx_x3f_2905_);
lean_ctor_set(v___x_2921_, 5, v_synthPendingDepth_2906_);
lean_ctor_set(v___x_2921_, 6, v_canUnfold_x3f_2907_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*7, v_trackZetaDelta_2901_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*7 + 1, v_univApprox_2908_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2909_);
lean_ctor_set_uint8(v___x_2921_, sizeof(void*)*7 + 3, v_cacheInferType_2910_);
v___x_2922_ = l_Lean_Meta_reduceRecMatcher_x3f(v___x_2801_, v___x_2921_, v_a_2797_, v_a_2798_, v_a_2799_);
lean_dec_ref_known(v___x_2921_, 7);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
if (lean_obj_tag(v_a_2923_) == 1)
{
lean_object* v_val_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2960_; 
lean_dec_ref_known(v_val_2807_, 1);
lean_del_object(v___x_2809_);
lean_dec_ref(v___x_2801_);
v_val_2924_ = lean_ctor_get(v_a_2923_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2923_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2926_ = v_a_2923_;
v_isShared_2927_ = v_isSharedCheck_2960_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_val_2924_);
lean_dec(v_a_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2960_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2924_, v_a_2795_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v_a_2929_; lean_object* v___x_2930_; 
v_a_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_a_2929_);
lean_dec_ref_known(v___x_2928_, 1);
v___x_2930_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_2786_, v_target_2787_, v_info_2788_, v_a_2929_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2943_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2933_ = v___x_2930_;
v_isShared_2934_ = v_isSharedCheck_2943_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2930_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2943_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2938_; 
v___x_2935_ = lean_box(0);
v___x_2936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2936_, 0, v_a_2931_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2936_);
v___x_2938_ = v___x_2926_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2936_);
v___x_2938_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
lean_object* v___x_2940_; 
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2938_);
v___x_2940_ = v___x_2933_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2926_);
v_a_2944_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2930_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2930_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
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
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2926_);
lean_dec_ref(v_info_2788_);
lean_dec_ref(v_target_2787_);
lean_dec(v_goal_2786_);
v_a_2952_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2928_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2928_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
else
{
lean_dec(v_a_2923_);
lean_dec_ref(v_target_2787_);
v___y_2812_ = v_a_2789_;
v___y_2813_ = v_a_2790_;
v___y_2814_ = v_a_2791_;
v___y_2815_ = v_a_2792_;
v___y_2816_ = v_a_2793_;
v___y_2817_ = v_a_2794_;
v___y_2818_ = v_a_2795_;
v___y_2819_ = v_a_2796_;
v___y_2820_ = v_a_2797_;
v___y_2821_ = v_a_2798_;
v___y_2822_ = v_a_2799_;
goto v___jp_2811_;
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref_known(v_val_2807_, 1);
lean_del_object(v___x_2809_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v_info_2788_);
lean_dec_ref(v_target_2787_);
lean_dec(v_goal_2786_);
v_a_2961_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2922_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2922_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_target_2787_);
v___y_2812_ = v_a_2789_;
v___y_2813_ = v_a_2790_;
v___y_2814_ = v_a_2791_;
v___y_2815_ = v_a_2792_;
v___y_2816_ = v_a_2793_;
v___y_2817_ = v_a_2794_;
v___y_2818_ = v_a_2795_;
v___y_2819_ = v_a_2796_;
v___y_2820_ = v_a_2797_;
v___y_2821_ = v_a_2798_;
v___y_2822_ = v_a_2799_;
goto v___jp_2811_;
}
v___jp_2811_:
{
lean_object* v___x_2823_; 
v___x_2823_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleForSplitCached___redArg(v_val_2807_, v_info_2788_, v___y_2813_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__1);
v___x_2826_ = l_Lean_indentExpr(v___x_2801_);
lean_inc_ref(v___x_2826_);
v___x_2827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2827_);
v___x_2829_ = v___x_2809_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_a_2824_, v_goal_2786_, v___x_2829_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
if (lean_obj_tag(v_a_2831_) == 1)
{
lean_object* v_mvarIds_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v___x_2826_);
v_mvarIds_2832_ = lean_ctor_get(v_a_2831_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2834_ = v_a_2831_;
v_isShared_2835_ = v_isSharedCheck_2858_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_mvarIds_2832_);
lean_dec(v_a_2831_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2858_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f___closed__0));
v___x_2837_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_mvarIds_2832_, v___x_2836_, v___y_2812_, v___y_2813_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
lean_dec(v_mvarIds_2832_);
if (lean_obj_tag(v___x_2837_) == 0)
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2849_; 
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2842_ = lean_array_to_list(v_a_2838_);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v___x_2842_);
v___x_2844_ = v___x_2834_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
lean_object* v___x_2846_; 
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2844_);
v___x_2846_ = v___x_2840_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_del_object(v___x_2834_);
v_a_2850_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2837_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2837_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_dec(v_a_2831_);
v___x_2859_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___closed__3);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___x_2859_);
lean_ctor_set(v___x_2860_, 1, v___x_2826_);
v___x_2861_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_2860_, v___y_2819_, v___y_2820_, v___y_2821_, v___y_2822_);
return v___x_2861_;
}
}
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec_ref(v___x_2826_);
v_a_2862_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2830_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2830_);
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
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_del_object(v___x_2809_);
lean_dec_ref(v___x_2801_);
lean_dec(v_goal_2786_);
v_a_2871_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2823_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2823_);
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
}
}
else
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec(v_a_2803_);
lean_dec_ref(v___x_2801_);
lean_dec_ref(v_info_2788_);
lean_dec_ref(v_target_2787_);
lean_dec(v_goal_2786_);
v___x_2972_ = lean_box(0);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2972_);
v___x_2974_ = v___x_2805_;
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
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_dec_ref(v___x_2801_);
lean_dec_ref(v_info_2788_);
lean_dec_ref(v_target_2787_);
lean_dec(v_goal_2786_);
v_a_2977_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2802_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2802_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f___boxed(lean_object* v_goal_2985_, lean_object* v_target_2986_, lean_object* v_info_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_2985_, v_target_2986_, v_info_2987_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_);
lean_dec(v_a_2998_);
lean_dec_ref(v_a_2997_);
lean_dec(v_a_2996_);
lean_dec_ref(v_a_2995_);
lean_dec(v_a_2994_);
lean_dec_ref(v_a_2993_);
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(lean_object* v_as_3001_, lean_object* v_as_x27_3002_, lean_object* v_b_3003_, lean_object* v_a_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___redArg(v_as_x27_3002_, v_b_3003_, v___y_3005_, v___y_3006_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0___boxed(lean_object* v_as_3018_, lean_object* v_as_x27_3019_, lean_object* v_b_3020_, lean_object* v_a_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_List_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f_spec__0(v_as_3018_, v_as_x27_3019_, v_b_3020_, v_a_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
lean_dec(v___y_3030_);
lean_dec_ref(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v_as_x27_3019_);
lean_dec(v_as_3018_);
return v_res_3034_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__0));
v___x_3037_ = l_Lean_stringToMessageData(v___x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(lean_object* v_goal_3038_, lean_object* v_target_3039_, lean_object* v_info_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_){
_start:
{
lean_object* v___x_3053_; lean_object* v_f_3054_; lean_object* v___x_3055_; 
v___x_3053_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3040_);
v_f_3054_ = l_Lean_Expr_getAppFn(v___x_3053_);
v___x_3055_ = l_Lean_Expr_fvarId_x3f(v_f_3054_);
lean_dec_ref(v_f_3054_);
if (lean_obj_tag(v___x_3055_) == 1)
{
lean_object* v_val_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; 
v_val_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc_n(v_val_3056_, 2);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = 0;
v___x_3058_ = l_Lean_FVarId_getValue_x3f___redArg(v_val_3056_, v___x_3057_, v_a_3048_, v_a_3050_, v_a_3051_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3146_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3061_ = v___x_3058_;
v_isShared_3062_ = v_isSharedCheck_3146_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_a_3059_);
lean_dec(v___x_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3146_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
if (lean_obj_tag(v_a_3059_) == 1)
{
lean_object* v_val_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3141_; 
lean_del_object(v___x_3061_);
v_val_3063_ = lean_ctor_get(v_a_3059_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_a_3059_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3065_ = v_a_3059_;
v_isShared_3066_ = v_isSharedCheck_3141_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_val_3063_);
lean_dec(v_a_3059_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3141_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v_options_3113_; uint8_t v_hasTrace_3114_; 
v_options_3113_ = lean_ctor_get(v_a_3050_, 2);
v_hasTrace_3114_ = lean_ctor_get_uint8(v_options_3113_, sizeof(void*)*1);
if (v_hasTrace_3114_ == 0)
{
lean_dec(v_val_3056_);
v___y_3068_ = v_a_3041_;
v___y_3069_ = v_a_3042_;
v___y_3070_ = v_a_3043_;
v___y_3071_ = v_a_3044_;
v___y_3072_ = v_a_3045_;
v___y_3073_ = v_a_3046_;
v___y_3074_ = v_a_3047_;
v___y_3075_ = v_a_3048_;
v___y_3076_ = v_a_3049_;
v___y_3077_ = v_a_3050_;
v___y_3078_ = v_a_3051_;
goto v___jp_3067_;
}
else
{
lean_object* v_inheritedTraceOptions_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v_inheritedTraceOptions_3115_ = lean_ctor_get(v_a_3050_, 13);
v___x_3116_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3117_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3118_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3115_, v_options_3113_, v___x_3117_);
if (v___x_3118_ == 0)
{
lean_dec(v_val_3056_);
v___y_3068_ = v_a_3041_;
v___y_3069_ = v_a_3042_;
v___y_3070_ = v_a_3043_;
v___y_3071_ = v_a_3044_;
v___y_3072_ = v_a_3045_;
v___y_3073_ = v_a_3046_;
v___y_3074_ = v_a_3047_;
v___y_3075_ = v_a_3048_;
v___y_3076_ = v_a_3049_;
v___y_3077_ = v_a_3050_;
v___y_3078_ = v_a_3051_;
goto v___jp_3067_;
}
else
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_FVarId_getUserName___redArg(v_val_3056_, v_a_3048_, v_a_3050_, v_a_3051_);
if (lean_obj_tag(v___x_3119_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
lean_inc(v_a_3120_);
lean_dec_ref_known(v___x_3119_, 1);
v___x_3121_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___closed__1);
v___x_3122_ = l_Lean_MessageData_ofName(v_a_3120_);
v___x_3123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3121_);
lean_ctor_set(v___x_3123_, 1, v___x_3122_);
v___x_3124_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3116_, v___x_3123_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_dec_ref_known(v___x_3124_, 1);
v___y_3068_ = v_a_3041_;
v___y_3069_ = v_a_3042_;
v___y_3070_ = v_a_3043_;
v___y_3071_ = v_a_3044_;
v___y_3072_ = v_a_3045_;
v___y_3073_ = v_a_3046_;
v___y_3074_ = v_a_3047_;
v___y_3075_ = v_a_3048_;
v___y_3076_ = v_a_3049_;
v___y_3077_ = v_a_3050_;
v___y_3078_ = v_a_3051_;
goto v___jp_3067_;
}
else
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
lean_del_object(v___x_3065_);
lean_dec(v_val_3063_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_info_3040_);
lean_dec_ref(v_target_3039_);
lean_dec(v_goal_3038_);
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v___x_3124_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v___x_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
lean_del_object(v___x_3065_);
lean_dec(v_val_3063_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_info_3040_);
lean_dec_ref(v_target_3039_);
lean_dec(v_goal_3038_);
v_a_3133_ = lean_ctor_get(v___x_3119_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3119_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3119_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3119_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
}
v___jp_3067_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3079_ = l_Lean_Expr_getAppNumArgs(v___x_3053_);
v___x_3080_ = lean_mk_empty_array_with_capacity(v___x_3079_);
lean_dec(v___x_3079_);
v___x_3081_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3053_, v___x_3080_);
v___x_3082_ = l_Lean_Expr_betaRev(v_val_3063_, v___x_3081_, v___x_3057_, v___x_3057_);
lean_dec_ref(v___x_3081_);
v___x_3083_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_3082_, v___y_3074_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3038_, v_target_3039_, v_info_3040_, v_a_3084_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3096_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3096_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3066_ == 0)
{
lean_ctor_set(v___x_3065_, 0, v_a_3086_);
v___x_3091_ = v___x_3065_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3091_);
v___x_3093_ = v___x_3088_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_del_object(v___x_3065_);
v_a_3097_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3085_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3085_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_del_object(v___x_3065_);
lean_dec_ref(v_info_3040_);
lean_dec_ref(v_target_3039_);
lean_dec(v_goal_3038_);
v_a_3105_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3083_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3083_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
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
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
lean_dec(v_a_3059_);
lean_dec(v_val_3056_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_info_3040_);
lean_dec_ref(v_target_3039_);
lean_dec(v_goal_3038_);
v___x_3142_ = lean_box(0);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3142_);
v___x_3144_ = v___x_3061_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_dec(v_val_3056_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_info_3040_);
lean_dec_ref(v_target_3039_);
lean_dec(v_goal_3038_);
v_a_3147_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3058_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3058_);
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
lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec(v___x_3055_);
lean_dec_ref(v___x_3053_);
lean_dec_ref(v_info_3040_);
lean_dec_ref(v_target_3039_);
lean_dec(v_goal_3038_);
v___x_3155_ = lean_box(0);
v___x_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f___boxed(lean_object* v_goal_3157_, lean_object* v_target_3158_, lean_object* v_info_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_3157_, v_target_3158_, v_info_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
lean_dec_ref(v_a_3165_);
lean_dec(v_a_3164_);
lean_dec_ref(v_a_3163_);
lean_dec(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
return v_res_3172_;
}
}
static uint64_t _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0(void){
_start:
{
uint8_t v___x_3173_; uint64_t v___x_3174_; 
v___x_3173_ = 3;
v___x_3174_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(lean_object* v_goal_3175_, lean_object* v_target_3176_, lean_object* v_info_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_, lean_object* v_a_3181_, lean_object* v_a_3182_, lean_object* v_a_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_){
_start:
{
lean_object* v___x_3190_; lean_object* v_a_3192_; lean_object* v_f_3253_; 
v___x_3190_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3177_);
v_f_3253_ = l_Lean_Expr_getAppFn(v___x_3190_);
if (lean_obj_tag(v_f_3253_) == 11)
{
lean_object* v___x_3254_; uint8_t v_foApprox_3255_; uint8_t v_ctxApprox_3256_; uint8_t v_quasiPatternApprox_3257_; uint8_t v_constApprox_3258_; uint8_t v_isDefEqStuckEx_3259_; uint8_t v_unificationHints_3260_; uint8_t v_proofIrrelevance_3261_; uint8_t v_assignSyntheticOpaque_3262_; uint8_t v_offsetCnstrs_3263_; uint8_t v_etaStruct_3264_; uint8_t v_univApprox_3265_; uint8_t v_iota_3266_; uint8_t v_beta_3267_; uint8_t v_proj_3268_; uint8_t v_zeta_3269_; uint8_t v_zetaDelta_3270_; uint8_t v_zetaUnused_3271_; uint8_t v_zetaHave_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3309_; 
v___x_3254_ = l_Lean_Meta_Context_config(v_a_3185_);
v_foApprox_3255_ = lean_ctor_get_uint8(v___x_3254_, 0);
v_ctxApprox_3256_ = lean_ctor_get_uint8(v___x_3254_, 1);
v_quasiPatternApprox_3257_ = lean_ctor_get_uint8(v___x_3254_, 2);
v_constApprox_3258_ = lean_ctor_get_uint8(v___x_3254_, 3);
v_isDefEqStuckEx_3259_ = lean_ctor_get_uint8(v___x_3254_, 4);
v_unificationHints_3260_ = lean_ctor_get_uint8(v___x_3254_, 5);
v_proofIrrelevance_3261_ = lean_ctor_get_uint8(v___x_3254_, 6);
v_assignSyntheticOpaque_3262_ = lean_ctor_get_uint8(v___x_3254_, 7);
v_offsetCnstrs_3263_ = lean_ctor_get_uint8(v___x_3254_, 8);
v_etaStruct_3264_ = lean_ctor_get_uint8(v___x_3254_, 10);
v_univApprox_3265_ = lean_ctor_get_uint8(v___x_3254_, 11);
v_iota_3266_ = lean_ctor_get_uint8(v___x_3254_, 12);
v_beta_3267_ = lean_ctor_get_uint8(v___x_3254_, 13);
v_proj_3268_ = lean_ctor_get_uint8(v___x_3254_, 14);
v_zeta_3269_ = lean_ctor_get_uint8(v___x_3254_, 15);
v_zetaDelta_3270_ = lean_ctor_get_uint8(v___x_3254_, 16);
v_zetaUnused_3271_ = lean_ctor_get_uint8(v___x_3254_, 17);
v_zetaHave_3272_ = lean_ctor_get_uint8(v___x_3254_, 18);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3274_ = v___x_3254_;
v_isShared_3275_ = v_isSharedCheck_3309_;
goto v_resetjp_3273_;
}
else
{
lean_dec(v___x_3254_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3309_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
uint8_t v_trackZetaDelta_3276_; lean_object* v_zetaDeltaSet_3277_; lean_object* v_lctx_3278_; lean_object* v_localInstances_3279_; lean_object* v_defEqCtx_x3f_3280_; lean_object* v_synthPendingDepth_3281_; lean_object* v_canUnfold_x3f_3282_; uint8_t v_univApprox_3283_; uint8_t v_inTypeClassResolution_3284_; uint8_t v_cacheInferType_3285_; uint8_t v___x_3286_; lean_object* v_config_3288_; 
v_trackZetaDelta_3276_ = lean_ctor_get_uint8(v_a_3185_, sizeof(void*)*7);
v_zetaDeltaSet_3277_ = lean_ctor_get(v_a_3185_, 1);
v_lctx_3278_ = lean_ctor_get(v_a_3185_, 2);
v_localInstances_3279_ = lean_ctor_get(v_a_3185_, 3);
v_defEqCtx_x3f_3280_ = lean_ctor_get(v_a_3185_, 4);
v_synthPendingDepth_3281_ = lean_ctor_get(v_a_3185_, 5);
v_canUnfold_x3f_3282_ = lean_ctor_get(v_a_3185_, 6);
v_univApprox_3283_ = lean_ctor_get_uint8(v_a_3185_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3284_ = lean_ctor_get_uint8(v_a_3185_, sizeof(void*)*7 + 2);
v_cacheInferType_3285_ = lean_ctor_get_uint8(v_a_3185_, sizeof(void*)*7 + 3);
v___x_3286_ = 3;
if (v_isShared_3275_ == 0)
{
v_config_3288_ = v___x_3274_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 0, v_foApprox_3255_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 1, v_ctxApprox_3256_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 2, v_quasiPatternApprox_3257_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 3, v_constApprox_3258_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 4, v_isDefEqStuckEx_3259_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 5, v_unificationHints_3260_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 6, v_proofIrrelevance_3261_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 7, v_assignSyntheticOpaque_3262_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 8, v_offsetCnstrs_3263_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 10, v_etaStruct_3264_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 11, v_univApprox_3265_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 12, v_iota_3266_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 13, v_beta_3267_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 14, v_proj_3268_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 15, v_zeta_3269_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 16, v_zetaDelta_3270_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 17, v_zetaUnused_3271_);
lean_ctor_set_uint8(v_reuseFailAlloc_3308_, 18, v_zetaHave_3272_);
v_config_3288_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
uint64_t v___x_3289_; uint64_t v___x_3290_; uint64_t v___x_3291_; uint64_t v___x_3292_; uint64_t v___x_3293_; uint64_t v_key_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
lean_ctor_set_uint8(v_config_3288_, 9, v___x_3286_);
v___x_3289_ = l_Lean_Meta_Context_configKey(v_a_3185_);
v___x_3290_ = 3ULL;
v___x_3291_ = lean_uint64_shift_right(v___x_3289_, v___x_3290_);
v___x_3292_ = lean_uint64_shift_left(v___x_3291_, v___x_3290_);
v___x_3293_ = lean_uint64_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___closed__0);
v_key_3294_ = lean_uint64_lor(v___x_3292_, v___x_3293_);
v___x_3295_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3295_, 0, v_config_3288_);
lean_ctor_set_uint64(v___x_3295_, sizeof(void*)*1, v_key_3294_);
lean_inc(v_canUnfold_x3f_3282_);
lean_inc(v_synthPendingDepth_3281_);
lean_inc(v_defEqCtx_x3f_3280_);
lean_inc_ref(v_localInstances_3279_);
lean_inc_ref(v_lctx_3278_);
lean_inc(v_zetaDeltaSet_3277_);
v___x_3296_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3296_, 0, v___x_3295_);
lean_ctor_set(v___x_3296_, 1, v_zetaDeltaSet_3277_);
lean_ctor_set(v___x_3296_, 2, v_lctx_3278_);
lean_ctor_set(v___x_3296_, 3, v_localInstances_3279_);
lean_ctor_set(v___x_3296_, 4, v_defEqCtx_x3f_3280_);
lean_ctor_set(v___x_3296_, 5, v_synthPendingDepth_3281_);
lean_ctor_set(v___x_3296_, 6, v_canUnfold_x3f_3282_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7, v_trackZetaDelta_3276_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7 + 1, v_univApprox_3283_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3284_);
lean_ctor_set_uint8(v___x_3296_, sizeof(void*)*7 + 3, v_cacheInferType_3285_);
v___x_3297_ = l_Lean_Meta_reduceProj_x3f(v_f_3253_, v___x_3296_, v_a_3186_, v_a_3187_, v_a_3188_);
lean_dec_ref_known(v___x_3296_, 7);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v_a_3192_ = v_a_3298_;
goto v___jp_3191_;
}
else
{
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3299_; 
v_a_3299_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3297_, 1);
v_a_3192_ = v_a_3299_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3307_; 
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_info_3177_);
lean_dec_ref(v_target_3176_);
lean_dec(v_goal_3175_);
v_a_3300_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3307_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3307_ == 0)
{
v___x_3302_ = v___x_3297_;
v_isShared_3303_ = v_isSharedCheck_3307_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_a_3300_);
lean_dec(v___x_3297_);
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
}
else
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
lean_dec_ref(v_f_3253_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_info_3177_);
lean_dec_ref(v_target_3176_);
lean_dec(v_goal_3175_);
v___x_3310_ = lean_box(0);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
v___jp_3191_:
{
if (lean_obj_tag(v_a_3192_) == 1)
{
lean_object* v_val_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3250_; 
v_val_3193_ = lean_ctor_get(v_a_3192_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_a_3192_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3195_ = v_a_3192_;
v_isShared_3196_ = v_isSharedCheck_3250_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_val_3193_);
lean_dec(v_a_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3250_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lean_Meta_Sym_unfoldReducible(v_val_3193_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v_a_3198_; lean_object* v___x_3199_; 
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc(v_a_3198_);
lean_dec_ref_known(v___x_3197_, 1);
v___x_3199_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3198_, v_a_3184_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v_a_3200_ = lean_ctor_get(v___x_3199_, 0);
lean_inc(v_a_3200_);
lean_dec_ref_known(v___x_3199_, 1);
v___x_3201_ = l_Lean_Expr_getAppNumArgs(v___x_3190_);
v___x_3202_ = lean_mk_empty_array_with_capacity(v___x_3201_);
lean_dec(v___x_3201_);
v___x_3203_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(v___x_3190_, v___x_3202_);
v___x_3204_ = l_Lean_Meta_Sym_betaRevS___redArg(v_a_3200_, v___x_3203_, v_a_3184_);
lean_dec_ref(v___x_3203_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v___x_3206_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_replaceProgDefEq(v_goal_3175_, v_target_3176_, v_info_3177_, v_a_3205_, v_a_3178_, v_a_3179_, v_a_3180_, v_a_3181_, v_a_3182_, v_a_3183_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, v_a_3188_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3217_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3209_ = v___x_3206_;
v_isShared_3210_ = v_isSharedCheck_3217_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3206_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3217_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_a_3207_);
v___x_3212_ = v___x_3195_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3214_; 
if (v_isShared_3210_ == 0)
{
lean_ctor_set(v___x_3209_, 0, v___x_3212_);
v___x_3214_ = v___x_3209_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v___x_3212_);
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
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
lean_del_object(v___x_3195_);
v_a_3218_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3206_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3206_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3195_);
lean_dec_ref(v_info_3177_);
lean_dec_ref(v_target_3176_);
lean_dec(v_goal_3175_);
v_a_3226_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3204_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3204_);
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
lean_del_object(v___x_3195_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_info_3177_);
lean_dec_ref(v_target_3176_);
lean_dec(v_goal_3175_);
v_a_3234_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3199_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3199_);
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
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_del_object(v___x_3195_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_info_3177_);
lean_dec_ref(v_target_3176_);
lean_dec(v_goal_3175_);
v_a_3242_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3197_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3197_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
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
}
else
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
lean_dec(v_a_3192_);
lean_dec_ref(v___x_3190_);
lean_dec_ref(v_info_3177_);
lean_dec_ref(v_target_3176_);
lean_dec(v_goal_3175_);
v___x_3251_ = lean_box(0);
v___x_3252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3252_, 0, v___x_3251_);
return v___x_3252_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f___boxed(lean_object* v_goal_3312_, lean_object* v_target_3313_, lean_object* v_info_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_3312_, v_target_3313_, v_info_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec_ref(v_a_3322_);
lean_dec(v_a_3321_);
lean_dec_ref(v_a_3320_);
lean_dec(v_a_3319_);
lean_dec_ref(v_a_3318_);
lean_dec(v_a_3317_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
return v_res_3327_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3329_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__0));
v___x_3330_ = l_Lean_stringToMessageData(v___x_3329_);
return v___x_3330_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3(void){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__2));
v___x_3333_ = l_Lean_stringToMessageData(v___x_3332_);
return v___x_3333_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5(void){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__4));
v___x_3336_ = l_Lean_stringToMessageData(v___x_3335_);
return v___x_3336_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7(void){
_start:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__6));
v___x_3339_ = l_Lean_stringToMessageData(v___x_3338_);
return v___x_3339_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
if (lean_obj_tag(v_a_3340_) == 0)
{
lean_object* v___x_3342_; 
v___x_3342_ = l_List_reverse___redArg(v_a_3341_);
return v___x_3342_;
}
else
{
lean_object* v_head_3343_; lean_object* v_tail_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3372_; 
v_head_3343_ = lean_ctor_get(v_a_3340_, 0);
v_tail_3344_ = lean_ctor_get(v_a_3340_, 1);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_a_3340_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3346_ = v_a_3340_;
v_isShared_3347_ = v_isSharedCheck_3372_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_tail_3344_);
lean_inc(v_head_3343_);
lean_dec(v_a_3340_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3372_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___y_3349_; 
switch(lean_obj_tag(v_head_3343_))
{
case 0:
{
lean_object* v_declName_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_declName_3354_ = lean_ctor_get(v_head_3343_, 0);
lean_inc(v_declName_3354_);
lean_dec_ref_known(v_head_3343_, 1);
v___x_3355_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3356_ = l_Lean_MessageData_ofName(v_declName_3354_);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3355_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___y_3349_ = v___x_3357_;
goto v___jp_3348_;
}
case 1:
{
lean_object* v_fvarId_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_fvarId_3358_ = lean_ctor_get(v_head_3343_, 0);
lean_inc(v_fvarId_3358_);
lean_dec_ref_known(v_head_3343_, 1);
v___x_3359_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3360_ = l_Lean_mkFVar(v_fvarId_3358_);
v___x_3361_ = l_Lean_MessageData_ofExpr(v___x_3360_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3359_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___y_3349_ = v___x_3362_;
goto v___jp_3348_;
}
default: 
{
lean_object* v_ref_3363_; lean_object* v_proof_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; 
v_ref_3363_ = lean_ctor_get(v_head_3343_, 1);
lean_inc(v_ref_3363_);
v_proof_3364_ = lean_ctor_get(v_head_3343_, 2);
lean_inc_ref(v_proof_3364_);
lean_dec_ref_known(v_head_3343_, 3);
v___x_3365_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3366_ = l_Lean_MessageData_ofSyntax(v_ref_3363_);
v___x_3367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3365_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
v___x_3368_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = l_Lean_MessageData_ofExpr(v_proof_3364_);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___y_3349_ = v___x_3371_;
goto v___jp_3348_;
}
}
v___jp_3348_:
{
lean_object* v___x_3351_; 
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v_a_3341_);
lean_ctor_set(v___x_3346_, 0, v___y_3349_);
v___x_3351_ = v___x_3346_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3353_; 
v_reuseFailAlloc_3353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___y_3349_);
lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_a_3341_);
v___x_3351_ = v_reuseFailAlloc_3353_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
v_a_3340_ = v_tail_3344_;
v_a_3341_ = v___x_3351_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(size_t v_sz_3373_, size_t v_i_3374_, lean_object* v_bs_3375_){
_start:
{
uint8_t v___x_3376_; 
v___x_3376_ = lean_usize_dec_lt(v_i_3374_, v_sz_3373_);
if (v___x_3376_ == 0)
{
return v_bs_3375_;
}
else
{
lean_object* v_v_3377_; lean_object* v_proof_3378_; lean_object* v___x_3379_; lean_object* v_bs_x27_3380_; size_t v___x_3381_; size_t v___x_3382_; lean_object* v___x_3383_; 
v_v_3377_ = lean_array_uget_borrowed(v_bs_3375_, v_i_3374_);
v_proof_3378_ = lean_ctor_get(v_v_3377_, 1);
lean_inc_ref(v_proof_3378_);
v___x_3379_ = lean_unsigned_to_nat(0u);
v_bs_x27_3380_ = lean_array_uset(v_bs_3375_, v_i_3374_, v___x_3379_);
v___x_3381_ = ((size_t)1ULL);
v___x_3382_ = lean_usize_add(v_i_3374_, v___x_3381_);
v___x_3383_ = lean_array_uset(v_bs_x27_3380_, v_i_3374_, v_proof_3378_);
v_i_3374_ = v___x_3382_;
v_bs_3375_ = v___x_3383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0___boxed(lean_object* v_sz_3385_, lean_object* v_i_3386_, lean_object* v_bs_3387_){
_start:
{
size_t v_sz_boxed_3388_; size_t v_i_boxed_3389_; lean_object* v_res_3390_; 
v_sz_boxed_3388_ = lean_unbox_usize(v_sz_3385_);
lean_dec(v_sz_3385_);
v_i_boxed_3389_ = lean_unbox_usize(v_i_3386_);
lean_dec(v_i_3386_);
v_res_3390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_boxed_3388_, v_i_boxed_3389_, v_bs_3387_);
return v_res_3390_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1(void){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__0));
v___x_3393_ = l_Lean_stringToMessageData(v___x_3392_);
return v___x_3393_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__2));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__4));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__6));
v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
return v___x_3402_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9(void){
_start:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__8));
v___x_3405_ = l_Lean_stringToMessageData(v___x_3404_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(lean_object* v_prog_3406_, lean_object* v_monad_3407_, lean_object* v_thms_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_){
_start:
{
uint8_t v_errorOnMissingSpec_3415_; 
v_errorOnMissingSpec_3415_ = lean_ctor_get_uint8(v_a_3409_, sizeof(void*)*4 + 2);
if (v_errorOnMissingSpec_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3416_ = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(v___x_3416_, 0, v_prog_3406_);
lean_ctor_set(v___x_3416_, 1, v_monad_3407_);
lean_ctor_set(v___x_3416_, 2, v_thms_3408_);
v___x_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
v___x_3418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; uint8_t v___x_3421_; 
v___x_3419_ = lean_array_get_size(v_thms_3408_);
v___x_3420_ = lean_unsigned_to_nat(0u);
v___x_3421_ = lean_nat_dec_eq(v___x_3419_, v___x_3420_);
if (v___x_3421_ == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; size_t v_sz_3431_; size_t v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v___x_3422_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__1);
v___x_3423_ = l_Lean_MessageData_ofExpr(v_monad_3407_);
v___x_3424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__3);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_MessageData_ofExpr(v_prog_3406_);
v___x_3428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__5);
v___x_3430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v_sz_3431_ = lean_array_size(v_thms_3408_);
v___x_3432_ = ((size_t)0ULL);
v___x_3433_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__0(v_sz_3431_, v___x_3432_, v_thms_3408_);
v___x_3434_ = lean_array_to_list(v___x_3433_);
v___x_3435_ = lean_box(0);
v___x_3436_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1(v___x_3434_, v___x_3435_);
v___x_3437_ = l_Lean_MessageData_ofList(v___x_3436_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3430_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
v___x_3441_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3440_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
return v___x_3441_;
}
else
{
lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
lean_dec_ref(v_thms_3408_);
lean_dec_ref(v_monad_3407_);
v___x_3442_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__9);
v___x_3443_ = l_Lean_MessageData_ofExpr(v_prog_3406_);
v___x_3444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3444_, 0, v___x_3442_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___closed__7);
v___x_3446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3446_, 0, v___x_3444_);
lean_ctor_set(v___x_3446_, 1, v___x_3445_);
v___x_3447_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3446_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_);
return v___x_3447_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg___boxed(lean_object* v_prog_3448_, lean_object* v_monad_3449_, lean_object* v_thms_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3448_, v_monad_3449_, v_thms_3450_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec_ref(v_a_3451_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(lean_object* v_prog_3458_, lean_object* v_monad_3459_, lean_object* v_thms_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v_prog_3458_, v_monad_3459_, v_thms_3460_, v_a_3461_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___boxed(lean_object* v_prog_3474_, lean_object* v_monad_3475_, lean_object* v_thms_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v_res_3489_; 
v_res_3489_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec(v_prog_3474_, v_monad_3475_, v_thms_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec(v_a_3478_);
lean_dec_ref(v_a_3477_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
if (lean_obj_tag(v_a_3490_) == 0)
{
lean_object* v___x_3492_; 
v___x_3492_ = l_List_reverse___redArg(v_a_3491_);
return v___x_3492_;
}
else
{
lean_object* v_head_3493_; lean_object* v_tail_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3503_; 
v_head_3493_ = lean_ctor_get(v_a_3490_, 0);
v_tail_3494_ = lean_ctor_get(v_a_3490_, 1);
v_isSharedCheck_3503_ = !lean_is_exclusive(v_a_3490_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3496_ = v_a_3490_;
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_tail_3494_);
lean_inc(v_head_3493_);
lean_dec(v_a_3490_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3503_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = l_Lean_MessageData_ofExpr(v_head_3493_);
if (v_isShared_3497_ == 0)
{
lean_ctor_set(v___x_3496_, 1, v_a_3491_);
lean_ctor_set(v___x_3496_, 0, v___x_3498_);
v___x_3500_ = v___x_3496_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_a_3491_);
v___x_3500_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
v_a_3490_ = v_tail_3494_;
v_a_3491_ = v___x_3500_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__0));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3(void){
_start:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__2));
v___x_3509_ = l_Lean_stringToMessageData(v___x_3508_);
return v___x_3509_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5(void){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__4));
v___x_3512_ = l_Lean_stringToMessageData(v___x_3511_);
return v___x_3512_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__6));
v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__8));
v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
return v___x_3518_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11(void){
_start:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__10));
v___x_3521_ = l_Lean_stringToMessageData(v___x_3520_);
return v___x_3521_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13(void){
_start:
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__12));
v___x_3524_ = l_Lean_stringToMessageData(v___x_3523_);
return v___x_3524_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__14));
v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__16));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__18));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__20));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23(void){
_start:
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
v___x_3538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__22));
v___x_3539_ = l_Lean_stringToMessageData(v___x_3538_);
return v___x_3539_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25(void){
_start:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__24));
v___x_3542_ = l_Lean_stringToMessageData(v___x_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(lean_object* v_scope_3543_, lean_object* v_goal_3544_, lean_object* v_target_3545_, lean_object* v_info_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3691_; lean_object* v___y_3692_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v___y_3729_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; uint8_t v___y_3744_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v___y_3768_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_options_3783_; lean_object* v_inheritedTraceOptions_3784_; uint8_t v_hasTrace_3785_; lean_object* v_cls_3786_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; 
v_options_3783_ = lean_ctor_get(v_a_3556_, 2);
v_inheritedTraceOptions_3784_ = lean_ctor_get(v_a_3556_, 13);
v_hasTrace_3785_ = lean_ctor_get_uint8(v_options_3783_, sizeof(void*)*1);
v_cls_3786_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_3785_ == 0)
{
v___y_3814_ = v_a_3547_;
v___y_3815_ = v_a_3548_;
v___y_3816_ = v_a_3549_;
v___y_3817_ = v_a_3550_;
v___y_3818_ = v_a_3551_;
v___y_3819_ = v_a_3552_;
v___y_3820_ = v_a_3553_;
v___y_3821_ = v_a_3554_;
v___y_3822_ = v_a_3555_;
v___y_3823_ = v_a_3556_;
v___y_3824_ = v_a_3557_;
goto v___jp_3813_;
}
else
{
lean_object* v___x_3871_; uint8_t v___x_3872_; 
v___x_3871_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3872_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3784_, v_options_3783_, v___x_3871_);
if (v___x_3872_ == 0)
{
v___y_3814_ = v_a_3547_;
v___y_3815_ = v_a_3548_;
v___y_3816_ = v_a_3549_;
v___y_3817_ = v_a_3550_;
v___y_3818_ = v_a_3551_;
v___y_3819_ = v_a_3552_;
v___y_3820_ = v_a_3553_;
v___y_3821_ = v_a_3554_;
v___y_3822_ = v_a_3555_;
v___y_3823_ = v_a_3556_;
v___y_3824_ = v_a_3557_;
goto v___jp_3813_;
}
else
{
lean_object* v_excessArgs_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_excessArgs_3873_ = lean_ctor_get(v_info_3546_, 2);
v___x_3874_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__23);
v___x_3875_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3546_);
v___x_3876_ = l_Lean_MessageData_ofExpr(v___x_3875_);
v___x_3877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3874_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
v___x_3878_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__25);
v___x_3879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3879_, 0, v___x_3877_);
lean_ctor_set(v___x_3879_, 1, v___x_3878_);
lean_inc_ref(v_excessArgs_3873_);
v___x_3880_ = lean_array_to_list(v_excessArgs_3873_);
v___x_3881_ = lean_box(0);
v___x_3882_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3880_, v___x_3881_);
v___x_3883_ = l_Lean_MessageData_ofList(v___x_3882_);
v___x_3884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3879_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3786_, v___x_3884_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_dec_ref_known(v___x_3885_, 1);
v___y_3814_ = v_a_3547_;
v___y_3815_ = v_a_3548_;
v___y_3816_ = v_a_3549_;
v___y_3817_ = v_a_3550_;
v___y_3818_ = v_a_3551_;
v___y_3819_ = v_a_3552_;
v___y_3820_ = v_a_3553_;
v___y_3821_ = v_a_3554_;
v___y_3822_ = v_a_3555_;
v___y_3823_ = v_a_3556_;
v___y_3824_ = v_a_3557_;
goto v___jp_3813_;
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
lean_dec(v_goal_3544_);
lean_dec_ref(v_scope_3543_);
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
}
v___jp_3559_:
{
lean_object* v_excessArgs_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_excessArgs_3568_ = lean_ctor_get(v_info_3546_, 2);
lean_inc_ref(v_excessArgs_3568_);
lean_inc_ref(v___y_3564_);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___y_3564_);
lean_ctor_set(v___x_3569_, 1, v___y_3567_);
v___x_3570_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
lean_ctor_set(v___x_3572_, 1, v___y_3562_);
v___x_3573_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3572_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_Lean_indentExpr(v_target_3545_);
v___x_3576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3574_);
lean_ctor_set(v___x_3576_, 1, v___x_3575_);
v___x_3577_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3576_);
lean_ctor_set(v___x_3578_, 1, v___x_3577_);
v___x_3579_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_3546_);
lean_dec_ref(v_info_3546_);
v___x_3580_ = l_Lean_indentExpr(v___x_3579_);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3578_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3581_);
lean_ctor_set(v___x_3583_, 1, v___x_3582_);
v___x_3584_ = lean_array_to_list(v_excessArgs_3568_);
v___x_3585_ = lean_box(0);
v___x_3586_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3584_, v___x_3585_);
v___x_3587_ = l_Lean_MessageData_ofList(v___x_3586_);
v___x_3588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3583_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__9);
v___x_3590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3588_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = l_Lean_indentExpr(v___y_3561_);
v___x_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3592_, 0, v___x_3590_);
lean_ctor_set(v___x_3592_, 1, v___x_3591_);
v___x_3593_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3592_, v___y_3560_, v___y_3563_, v___y_3566_, v___y_3565_);
return v___x_3593_;
}
v___jp_3594_:
{
if (lean_obj_tag(v___y_3608_) == 0)
{
lean_object* v_a_3609_; 
v_a_3609_ = lean_ctor_get(v___y_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___y_3608_, 1);
if (lean_obj_tag(v_a_3609_) == 1)
{
lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3670_; 
v_val_3610_ = lean_ctor_get(v_a_3609_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v_a_3609_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3612_ = v_a_3609_;
v_isShared_3613_ = v_isSharedCheck_3670_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_dec(v_a_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3670_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3614_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__11);
v___x_3615_ = l_Lean_indentExpr(v___y_3606_);
lean_inc_ref(v___x_3615_);
v___x_3616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 0, v___x_3616_);
v___x_3618_ = v___x_3612_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3616_);
v___x_3618_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; 
lean_inc(v_val_3610_);
v___x_3619_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(v_val_3610_, v_goal_3544_, v___x_3618_, v___y_3605_, v___y_3599_, v___y_3603_, v___y_3597_, v___y_3602_, v___y_3601_, v___y_3595_, v___y_3598_, v___y_3604_, v___y_3596_, v___y_3607_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3660_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3622_ = v___x_3619_;
v_isShared_3623_ = v_isSharedCheck_3660_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3619_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3660_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
if (lean_obj_tag(v_a_3620_) == 1)
{
lean_object* v_mvarIds_3624_; lean_object* v___x_3625_; lean_object* v___x_3627_; 
lean_dec_ref(v___x_3615_);
lean_dec(v_val_3610_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
v_mvarIds_3624_ = lean_ctor_get(v_a_3620_, 0);
lean_inc(v_mvarIds_3624_);
lean_dec_ref_known(v_a_3620_, 1);
v___x_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3625_, 0, v_scope_3543_);
lean_ctor_set(v___x_3625_, 1, v_mvarIds_3624_);
if (v_isShared_3623_ == 0)
{
lean_ctor_set(v___x_3622_, 0, v___x_3625_);
v___x_3627_ = v___x_3622_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v___x_3625_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
else
{
lean_object* v_expr_3629_; lean_object* v___x_3630_; 
lean_del_object(v___x_3622_);
lean_dec(v_a_3620_);
lean_dec_ref(v_scope_3543_);
v_expr_3629_ = lean_ctor_get(v_val_3610_, 0);
lean_inc_ref(v_expr_3629_);
lean_dec(v_val_3610_);
lean_inc(v___y_3607_);
lean_inc_ref(v___y_3596_);
lean_inc(v___y_3604_);
lean_inc_ref(v___y_3598_);
v___x_3630_ = lean_infer_type(v_expr_3629_, v___y_3598_, v___y_3604_, v___y_3596_, v___y_3607_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v_proof_3632_; lean_object* v___x_3633_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
lean_inc(v_a_3631_);
lean_dec_ref_known(v___x_3630_, 1);
v_proof_3632_ = lean_ctor_get(v___y_3600_, 1);
lean_inc_ref(v_proof_3632_);
lean_dec_ref(v___y_3600_);
v___x_3633_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__13);
switch(lean_obj_tag(v_proof_3632_))
{
case 0:
{
lean_object* v_declName_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; 
v_declName_3634_ = lean_ctor_get(v_proof_3632_, 0);
lean_inc(v_declName_3634_);
lean_dec_ref_known(v_proof_3632_, 1);
v___x_3635_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
v___x_3636_ = l_Lean_MessageData_ofName(v_declName_3634_);
v___x_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___x_3635_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___y_3560_ = v___y_3598_;
v___y_3561_ = v_a_3631_;
v___y_3562_ = v___x_3615_;
v___y_3563_ = v___y_3604_;
v___y_3564_ = v___x_3633_;
v___y_3565_ = v___y_3607_;
v___y_3566_ = v___y_3596_;
v___y_3567_ = v___x_3637_;
goto v___jp_3559_;
}
case 1:
{
lean_object* v_fvarId_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_fvarId_3638_ = lean_ctor_get(v_proof_3632_, 0);
lean_inc(v_fvarId_3638_);
lean_dec_ref_known(v_proof_3632_, 1);
v___x_3639_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
v___x_3640_ = l_Lean_mkFVar(v_fvarId_3638_);
v___x_3641_ = l_Lean_MessageData_ofExpr(v___x_3640_);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3639_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___y_3560_ = v___y_3598_;
v___y_3561_ = v_a_3631_;
v___y_3562_ = v___x_3615_;
v___y_3563_ = v___y_3604_;
v___y_3564_ = v___x_3633_;
v___y_3565_ = v___y_3607_;
v___y_3566_ = v___y_3596_;
v___y_3567_ = v___x_3642_;
goto v___jp_3559_;
}
default: 
{
lean_object* v_ref_3643_; lean_object* v_proof_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_ref_3643_ = lean_ctor_get(v_proof_3632_, 1);
lean_inc(v_ref_3643_);
v_proof_3644_ = lean_ctor_get(v_proof_3632_, 2);
lean_inc_ref(v_proof_3644_);
lean_dec_ref_known(v_proof_3632_, 3);
v___x_3645_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
v___x_3646_ = l_Lean_MessageData_ofSyntax(v_ref_3643_);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = l_Lean_MessageData_ofExpr(v_proof_3644_);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3649_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___y_3560_ = v___y_3598_;
v___y_3561_ = v_a_3631_;
v___y_3562_ = v___x_3615_;
v___y_3563_ = v___y_3604_;
v___y_3564_ = v___x_3633_;
v___y_3565_ = v___y_3607_;
v___y_3566_ = v___y_3596_;
v___y_3567_ = v___x_3651_;
goto v___jp_3559_;
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec_ref(v___x_3615_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
v_a_3652_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3630_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3630_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
lean_dec_ref(v___x_3615_);
lean_dec(v_val_3610_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
lean_dec_ref(v_scope_3543_);
v_a_3661_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3619_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3619_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
}
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
lean_dec(v_a_3609_);
lean_dec_ref(v_target_3545_);
lean_dec(v_goal_3544_);
lean_dec_ref(v_scope_3543_);
v___x_3671_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_3546_);
lean_dec_ref(v_info_3546_);
v___x_3672_ = lean_unsigned_to_nat(1u);
v___x_3673_ = lean_mk_empty_array_with_capacity(v___x_3672_);
v___x_3674_ = lean_array_push(v___x_3673_, v___y_3600_);
v___x_3675_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___y_3606_, v___x_3671_, v___x_3674_, v___y_3605_, v___y_3598_, v___y_3604_, v___y_3596_, v___y_3607_);
return v___x_3675_;
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec_ref(v___y_3606_);
lean_dec_ref(v___y_3600_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
lean_dec(v_goal_3544_);
lean_dec_ref(v_scope_3543_);
v_a_3676_ = lean_ctor_get(v___y_3608_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___y_3608_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___y_3608_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___y_3608_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
v___jp_3684_:
{
lean_object* v_excessArgs_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; 
v_excessArgs_3701_ = lean_ctor_get(v_info_3546_, 2);
lean_inc_ref(v___y_3686_);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___y_3686_);
lean_ctor_set(v___x_3702_, 1, v___y_3700_);
v___x_3703_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__1);
v___x_3704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
lean_inc_ref(v___y_3698_);
v___x_3705_ = l_Lean_indentExpr(v___y_3698_);
v___x_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3704_);
lean_ctor_set(v___x_3706_, 1, v___x_3705_);
v___x_3707_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__15);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3706_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = l_Lean_Exception_toMessageData(v___y_3687_);
v___x_3710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__3);
v___x_3712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3710_);
lean_ctor_set(v___x_3712_, 1, v___x_3711_);
lean_inc_ref(v_target_3545_);
v___x_3713_ = l_Lean_indentExpr(v_target_3545_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3712_);
lean_ctor_set(v___x_3714_, 1, v___x_3713_);
v___x_3715_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__5);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3714_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_3546_);
v___x_3718_ = l_Lean_indentExpr(v___x_3717_);
v___x_3719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3716_);
lean_ctor_set(v___x_3719_, 1, v___x_3718_);
v___x_3720_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__7);
v___x_3721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
lean_inc_ref(v_excessArgs_3701_);
v___x_3722_ = lean_array_to_list(v_excessArgs_3701_);
v___x_3723_ = lean_box(0);
v___x_3724_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec_spec__0(v___x_3722_, v___x_3723_);
v___x_3725_ = l_Lean_MessageData_ofList(v___x_3724_);
v___x_3726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3721_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_3726_, v___y_3689_, v___y_3696_, v___y_3688_, v___y_3699_);
v___y_3595_ = v___y_3685_;
v___y_3596_ = v___y_3688_;
v___y_3597_ = v___y_3690_;
v___y_3598_ = v___y_3689_;
v___y_3599_ = v___y_3691_;
v___y_3600_ = v___y_3692_;
v___y_3601_ = v___y_3693_;
v___y_3602_ = v___y_3694_;
v___y_3603_ = v___y_3695_;
v___y_3604_ = v___y_3696_;
v___y_3605_ = v___y_3697_;
v___y_3606_ = v___y_3698_;
v___y_3607_ = v___y_3699_;
v___y_3608_ = v___x_3727_;
goto v___jp_3594_;
}
v___jp_3728_:
{
if (v___y_3744_ == 0)
{
lean_object* v_proof_3745_; lean_object* v___x_3746_; 
lean_dec_ref(v___y_3730_);
v_proof_3745_ = lean_ctor_get(v___y_3736_, 1);
v___x_3746_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__17);
switch(lean_obj_tag(v_proof_3745_))
{
case 0:
{
lean_object* v_declName_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_declName_3747_ = lean_ctor_get(v_proof_3745_, 0);
v___x_3748_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3747_);
v___x_3749_ = l_Lean_MessageData_ofName(v_declName_3747_);
v___x_3750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3748_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___y_3685_ = v___y_3729_;
v___y_3686_ = v___x_3746_;
v___y_3687_ = v___y_3731_;
v___y_3688_ = v___y_3732_;
v___y_3689_ = v___y_3733_;
v___y_3690_ = v___y_3734_;
v___y_3691_ = v___y_3735_;
v___y_3692_ = v___y_3736_;
v___y_3693_ = v___y_3737_;
v___y_3694_ = v___y_3738_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
v___y_3699_ = v___y_3743_;
v___y_3700_ = v___x_3750_;
goto v___jp_3684_;
}
case 1:
{
lean_object* v_fvarId_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_fvarId_3751_ = lean_ctor_get(v_proof_3745_, 0);
v___x_3752_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3751_);
v___x_3753_ = l_Lean_mkFVar(v_fvarId_3751_);
v___x_3754_ = l_Lean_MessageData_ofExpr(v___x_3753_);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3752_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___y_3685_ = v___y_3729_;
v___y_3686_ = v___x_3746_;
v___y_3687_ = v___y_3731_;
v___y_3688_ = v___y_3732_;
v___y_3689_ = v___y_3733_;
v___y_3690_ = v___y_3734_;
v___y_3691_ = v___y_3735_;
v___y_3692_ = v___y_3736_;
v___y_3693_ = v___y_3737_;
v___y_3694_ = v___y_3738_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
v___y_3699_ = v___y_3743_;
v___y_3700_ = v___x_3755_;
goto v___jp_3684_;
}
default: 
{
lean_object* v_ref_3756_; lean_object* v_proof_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v_ref_3756_ = lean_ctor_get(v_proof_3745_, 1);
v_proof_3757_ = lean_ctor_get(v_proof_3745_, 2);
v___x_3758_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3756_);
v___x_3759_ = l_Lean_MessageData_ofSyntax(v_ref_3756_);
v___x_3760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
lean_inc_ref(v_proof_3757_);
v___x_3763_ = l_Lean_MessageData_ofExpr(v_proof_3757_);
v___x_3764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3762_);
lean_ctor_set(v___x_3764_, 1, v___x_3763_);
v___y_3685_ = v___y_3729_;
v___y_3686_ = v___x_3746_;
v___y_3687_ = v___y_3731_;
v___y_3688_ = v___y_3732_;
v___y_3689_ = v___y_3733_;
v___y_3690_ = v___y_3734_;
v___y_3691_ = v___y_3735_;
v___y_3692_ = v___y_3736_;
v___y_3693_ = v___y_3737_;
v___y_3694_ = v___y_3738_;
v___y_3695_ = v___y_3739_;
v___y_3696_ = v___y_3740_;
v___y_3697_ = v___y_3741_;
v___y_3698_ = v___y_3742_;
v___y_3699_ = v___y_3743_;
v___y_3700_ = v___x_3764_;
goto v___jp_3684_;
}
}
}
else
{
lean_dec_ref(v___y_3731_);
v___y_3595_ = v___y_3729_;
v___y_3596_ = v___y_3732_;
v___y_3597_ = v___y_3734_;
v___y_3598_ = v___y_3733_;
v___y_3599_ = v___y_3735_;
v___y_3600_ = v___y_3736_;
v___y_3601_ = v___y_3737_;
v___y_3602_ = v___y_3738_;
v___y_3603_ = v___y_3739_;
v___y_3604_ = v___y_3740_;
v___y_3605_ = v___y_3741_;
v___y_3606_ = v___y_3742_;
v___y_3607_ = v___y_3743_;
v___y_3608_ = v___y_3730_;
goto v___jp_3594_;
}
}
v___jp_3765_:
{
lean_object* v___x_3779_; 
lean_inc_ref(v_info_3546_);
lean_inc_ref(v___y_3766_);
v___x_3779_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRuleFromSpecCached(v___y_3766_, v_info_3546_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_);
if (lean_obj_tag(v___x_3779_) == 0)
{
v___y_3595_ = v___y_3774_;
v___y_3596_ = v___y_3777_;
v___y_3597_ = v___y_3771_;
v___y_3598_ = v___y_3775_;
v___y_3599_ = v___y_3769_;
v___y_3600_ = v___y_3766_;
v___y_3601_ = v___y_3773_;
v___y_3602_ = v___y_3772_;
v___y_3603_ = v___y_3770_;
v___y_3604_ = v___y_3776_;
v___y_3605_ = v___y_3768_;
v___y_3606_ = v___y_3767_;
v___y_3607_ = v___y_3778_;
v___y_3608_ = v___x_3779_;
goto v___jp_3594_;
}
else
{
lean_object* v_a_3780_; uint8_t v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
v___x_3781_ = l_Lean_Exception_isInterrupt(v_a_3780_);
if (v___x_3781_ == 0)
{
uint8_t v___x_3782_; 
lean_inc(v_a_3780_);
v___x_3782_ = l_Lean_Exception_isRuntime(v_a_3780_);
v___y_3729_ = v___y_3774_;
v___y_3730_ = v___x_3779_;
v___y_3731_ = v_a_3780_;
v___y_3732_ = v___y_3777_;
v___y_3733_ = v___y_3775_;
v___y_3734_ = v___y_3771_;
v___y_3735_ = v___y_3769_;
v___y_3736_ = v___y_3766_;
v___y_3737_ = v___y_3773_;
v___y_3738_ = v___y_3772_;
v___y_3739_ = v___y_3770_;
v___y_3740_ = v___y_3776_;
v___y_3741_ = v___y_3768_;
v___y_3742_ = v___y_3767_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___x_3782_;
goto v___jp_3728_;
}
else
{
v___y_3729_ = v___y_3774_;
v___y_3730_ = v___x_3779_;
v___y_3731_ = v_a_3780_;
v___y_3732_ = v___y_3777_;
v___y_3733_ = v___y_3775_;
v___y_3734_ = v___y_3771_;
v___y_3735_ = v___y_3769_;
v___y_3736_ = v___y_3766_;
v___y_3737_ = v___y_3773_;
v___y_3738_ = v___y_3772_;
v___y_3739_ = v___y_3770_;
v___y_3740_ = v___y_3776_;
v___y_3741_ = v___y_3768_;
v___y_3742_ = v___y_3767_;
v___y_3743_ = v___y_3778_;
v___y_3744_ = v___x_3781_;
goto v___jp_3728_;
}
}
}
v___jp_3787_:
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___y_3792_);
lean_ctor_set(v___x_3803_, 1, v___y_3802_);
v___x_3804_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v_cls_3786_, v___x_3803_, v___y_3801_, v___y_3789_, v___y_3794_, v___y_3793_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_dec_ref_known(v___x_3804_, 1);
v___y_3766_ = v___y_3797_;
v___y_3767_ = v___y_3799_;
v___y_3768_ = v___y_3795_;
v___y_3769_ = v___y_3800_;
v___y_3770_ = v___y_3791_;
v___y_3771_ = v___y_3798_;
v___y_3772_ = v___y_3796_;
v___y_3773_ = v___y_3790_;
v___y_3774_ = v___y_3788_;
v___y_3775_ = v___y_3801_;
v___y_3776_ = v___y_3789_;
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___y_3793_;
goto v___jp_3765_;
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3812_; 
lean_dec_ref(v___y_3799_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
lean_dec(v_goal_3544_);
lean_dec_ref(v_scope_3543_);
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3812_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3810_; 
if (v_isShared_3808_ == 0)
{
v___x_3810_ = v___x_3807_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v_a_3805_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
}
v___jp_3813_:
{
lean_object* v_specs_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_specs_3825_ = lean_ctor_get(v_scope_3543_, 0);
v___x_3826_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_3546_);
lean_inc_ref(v___x_3826_);
lean_inc_ref(v_specs_3825_);
v___x_3827_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_findSpecs(v_specs_3825_, v___x_3826_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
if (lean_obj_tag(v_a_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec_ref(v_target_3545_);
lean_dec(v_goal_3544_);
lean_dec_ref(v_scope_3543_);
v_a_3829_ = lean_ctor_get(v_a_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v_a_3828_, 1);
v___x_3830_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_3546_);
lean_dec_ref(v_info_3546_);
v___x_3831_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec___redArg(v___x_3826_, v___x_3830_, v_a_3829_, v___y_3814_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
return v___x_3831_;
}
else
{
lean_object* v_options_3832_; uint8_t v_hasTrace_3833_; 
v_options_3832_ = lean_ctor_get(v___y_3823_, 2);
v_hasTrace_3833_ = lean_ctor_get_uint8(v_options_3832_, sizeof(void*)*1);
if (v_hasTrace_3833_ == 0)
{
lean_object* v_a_3834_; 
v_a_3834_ = lean_ctor_get(v_a_3828_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v_a_3828_, 1);
v___y_3766_ = v_a_3834_;
v___y_3767_ = v___x_3826_;
v___y_3768_ = v___y_3814_;
v___y_3769_ = v___y_3815_;
v___y_3770_ = v___y_3816_;
v___y_3771_ = v___y_3817_;
v___y_3772_ = v___y_3818_;
v___y_3773_ = v___y_3819_;
v___y_3774_ = v___y_3820_;
v___y_3775_ = v___y_3821_;
v___y_3776_ = v___y_3822_;
v___y_3777_ = v___y_3823_;
v___y_3778_ = v___y_3824_;
goto v___jp_3765_;
}
else
{
lean_object* v_a_3835_; lean_object* v_inheritedTraceOptions_3836_; lean_object* v___x_3837_; uint8_t v___x_3838_; 
v_a_3835_ = lean_ctor_get(v_a_3828_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v_a_3828_, 1);
v_inheritedTraceOptions_3836_ = lean_ctor_get(v___y_3823_, 13);
v___x_3837_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3838_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3836_, v_options_3832_, v___x_3837_);
if (v___x_3838_ == 0)
{
v___y_3766_ = v_a_3835_;
v___y_3767_ = v___x_3826_;
v___y_3768_ = v___y_3814_;
v___y_3769_ = v___y_3815_;
v___y_3770_ = v___y_3816_;
v___y_3771_ = v___y_3817_;
v___y_3772_ = v___y_3818_;
v___y_3773_ = v___y_3819_;
v___y_3774_ = v___y_3820_;
v___y_3775_ = v___y_3821_;
v___y_3776_ = v___y_3822_;
v___y_3777_ = v___y_3823_;
v___y_3778_ = v___y_3824_;
goto v___jp_3765_;
}
else
{
lean_object* v_proof_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v_proof_3839_ = lean_ctor_get(v_a_3835_, 1);
v___x_3840_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__19);
lean_inc_ref(v___x_3826_);
v___x_3841_ = l_Lean_MessageData_ofExpr(v___x_3826_);
v___x_3842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3842_, 0, v___x_3840_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
v___x_3843_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___closed__21);
v___x_3844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3842_);
lean_ctor_set(v___x_3844_, 1, v___x_3843_);
switch(lean_obj_tag(v_proof_3839_))
{
case 0:
{
lean_object* v_declName_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v_declName_3845_ = lean_ctor_get(v_proof_3839_, 0);
v___x_3846_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__1);
lean_inc(v_declName_3845_);
v___x_3847_ = l_Lean_MessageData_ofName(v_declName_3845_);
v___x_3848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3846_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3822_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3816_;
v___y_3792_ = v___x_3844_;
v___y_3793_ = v___y_3824_;
v___y_3794_ = v___y_3823_;
v___y_3795_ = v___y_3814_;
v___y_3796_ = v___y_3818_;
v___y_3797_ = v_a_3835_;
v___y_3798_ = v___y_3817_;
v___y_3799_ = v___x_3826_;
v___y_3800_ = v___y_3815_;
v___y_3801_ = v___y_3821_;
v___y_3802_ = v___x_3848_;
goto v___jp_3787_;
}
case 1:
{
lean_object* v_fvarId_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v_fvarId_3849_ = lean_ctor_get(v_proof_3839_, 0);
v___x_3850_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__3);
lean_inc(v_fvarId_3849_);
v___x_3851_ = l_Lean_mkFVar(v_fvarId_3849_);
v___x_3852_ = l_Lean_MessageData_ofExpr(v___x_3851_);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3850_);
lean_ctor_set(v___x_3853_, 1, v___x_3852_);
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3822_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3816_;
v___y_3792_ = v___x_3844_;
v___y_3793_ = v___y_3824_;
v___y_3794_ = v___y_3823_;
v___y_3795_ = v___y_3814_;
v___y_3796_ = v___y_3818_;
v___y_3797_ = v_a_3835_;
v___y_3798_ = v___y_3817_;
v___y_3799_ = v___x_3826_;
v___y_3800_ = v___y_3815_;
v___y_3801_ = v___y_3821_;
v___y_3802_ = v___x_3853_;
goto v___jp_3787_;
}
default: 
{
lean_object* v_ref_3854_; lean_object* v_proof_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_ref_3854_ = lean_ctor_get(v_proof_3839_, 1);
v_proof_3855_ = lean_ctor_get(v_proof_3839_, 2);
v___x_3856_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__5);
lean_inc(v_ref_3854_);
v___x_3857_ = l_Lean_MessageData_ofSyntax(v_ref_3854_);
v___x_3858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3857_);
v___x_3859_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7, &l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7_once, _init_l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_stopOrErrorOnMissingSpec_spec__1___closed__7);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3858_);
lean_ctor_set(v___x_3860_, 1, v___x_3859_);
lean_inc_ref(v_proof_3855_);
v___x_3861_ = l_Lean_MessageData_ofExpr(v_proof_3855_);
v___x_3862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3860_);
lean_ctor_set(v___x_3862_, 1, v___x_3861_);
v___y_3788_ = v___y_3820_;
v___y_3789_ = v___y_3822_;
v___y_3790_ = v___y_3819_;
v___y_3791_ = v___y_3816_;
v___y_3792_ = v___x_3844_;
v___y_3793_ = v___y_3824_;
v___y_3794_ = v___y_3823_;
v___y_3795_ = v___y_3814_;
v___y_3796_ = v___y_3818_;
v___y_3797_ = v_a_3835_;
v___y_3798_ = v___y_3817_;
v___y_3799_ = v___x_3826_;
v___y_3800_ = v___y_3815_;
v___y_3801_ = v___y_3821_;
v___y_3802_ = v___x_3862_;
goto v___jp_3787_;
}
}
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec_ref(v___x_3826_);
lean_dec_ref(v_info_3546_);
lean_dec_ref(v_target_3545_);
lean_dec(v_goal_3544_);
lean_dec_ref(v_scope_3543_);
v_a_3863_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3827_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3827_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec___boxed(lean_object* v_scope_3894_, lean_object* v_goal_3895_, lean_object* v_target_3896_, lean_object* v_info_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v_res_3910_; 
v_res_3910_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v_scope_3894_, v_goal_3895_, v_target_3896_, v_info_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_);
lean_dec(v_a_3908_);
lean_dec_ref(v_a_3907_);
lean_dec(v_a_3906_);
lean_dec_ref(v_a_3905_);
lean_dec(v_a_3904_);
lean_dec_ref(v_a_3903_);
lean_dec(v_a_3902_);
lean_dec_ref(v_a_3901_);
lean_dec(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec_ref(v_a_3898_);
return v_res_3910_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1(void){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__0));
v___x_3913_ = l_Lean_stringToMessageData(v___x_3912_);
return v___x_3913_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__2));
v___x_3916_ = l_Lean_stringToMessageData(v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(lean_object* v_m_3917_, lean_object* v_prog_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_untilPat_x3f_3927_; 
v_untilPat_x3f_3927_ = lean_ctor_get(v_a_3919_, 3);
if (lean_obj_tag(v_untilPat_x3f_3927_) == 1)
{
lean_object* v_val_3928_; lean_object* v___x_3929_; 
v_val_3928_ = lean_ctor_get(v_untilPat_x3f_3927_, 0);
v___x_3929_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force(v_val_3928_, v_m_3917_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3930_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3931_ = 1;
lean_inc_ref(v_prog_3918_);
v___x_3932_ = l_Lean_Meta_Sym_Pattern_match_x3f(v_a_3930_, v_prog_3918_, v___x_3931_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3979_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3979_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3979_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
if (lean_obj_tag(v_a_3933_) == 0)
{
uint8_t v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3940_; 
lean_dec_ref(v_prog_3918_);
v___x_3937_ = 0;
v___x_3938_ = lean_box(v___x_3937_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3938_);
v___x_3940_ = v___x_3935_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
else
{
lean_object* v_options_3942_; uint8_t v_hasTrace_3943_; 
lean_dec_ref_known(v_a_3933_, 1);
v_options_3942_ = lean_ctor_get(v_a_3924_, 2);
v_hasTrace_3943_ = lean_ctor_get_uint8(v_options_3942_, sizeof(void*)*1);
if (v_hasTrace_3943_ == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3946_; 
lean_dec_ref(v_prog_3918_);
v___x_3944_ = lean_box(v___x_3931_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3944_);
v___x_3946_ = v___x_3935_;
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
else
{
lean_object* v_inheritedTraceOptions_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v_inheritedTraceOptions_3948_ = lean_ctor_get(v_a_3924_, 13);
v___x_3949_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
v___x_3950_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_3951_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3948_, v_options_3942_, v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3954_; 
lean_dec_ref(v_prog_3918_);
v___x_3952_ = lean_box(v___x_3931_);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3952_);
v___x_3954_ = v___x_3935_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v___x_3952_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; 
lean_del_object(v___x_3935_);
v___x_3956_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__1);
v___x_3957_ = l_Lean_MessageData_ofExpr(v_prog_3918_);
v___x_3958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3956_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
v___x_3959_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___closed__3);
v___x_3960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3958_);
lean_ctor_set(v___x_3960_, 1, v___x_3959_);
v___x_3961_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_3949_, v___x_3960_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3969_; 
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; 
v_unused_3970_ = lean_ctor_get(v___x_3961_, 0);
lean_dec(v_unused_3970_);
v___x_3963_ = v___x_3961_;
v_isShared_3964_ = v_isSharedCheck_3969_;
goto v_resetjp_3962_;
}
else
{
lean_dec(v___x_3961_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3969_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v___x_3967_; 
v___x_3965_ = lean_box(v___x_3931_);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3965_);
v___x_3967_ = v___x_3963_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3965_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
v_a_3971_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3961_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3961_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
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
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v_prog_3918_);
v_a_3980_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3932_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3932_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec_ref(v_prog_3918_);
v_a_3988_ = lean_ctor_get(v___x_3929_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3929_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3929_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3929_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
uint8_t v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_dec_ref(v_prog_3918_);
lean_dec_ref(v_m_3917_);
v___x_3996_ = 0;
v___x_3997_ = lean_box(v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg___boxed(lean_object* v_m_3999_, lean_object* v_prog_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_m_3999_, v_prog_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec_ref(v_a_4001_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(lean_object* v_m_4010_, lean_object* v_prog_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v_m_4010_, v_prog_4011_, v_a_4012_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___boxed(lean_object* v_m_4025_, lean_object* v_prog_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
lean_object* v_res_4039_; 
v_res_4039_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern(v_m_4025_, v_prog_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
lean_dec(v_a_4037_);
lean_dec_ref(v_a_4036_);
lean_dec(v_a_4035_);
lean_dec_ref(v_a_4034_);
lean_dec(v_a_4033_);
lean_dec_ref(v_a_4032_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
return v_res_4039_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__0));
v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
return v___x_4042_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__2));
v___x_4045_ = l_Lean_stringToMessageData(v___x_4044_);
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__4));
v___x_4048_ = l_Lean_stringToMessageData(v___x_4047_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__6));
v___x_4051_ = l_Lean_stringToMessageData(v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(lean_object* v_goal_4054_, lean_object* v_scope_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
lean_object* v_g_4069_; lean_object* v_gs_4075_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4085_; lean_object* v_gs_4086_; lean_object* v___y_4090_; lean_object* v_g_4091_; lean_object* v___y_4092_; lean_object* v___x_4113_; 
v___x_4113_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v___y_4057_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4516_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4116_ = v___x_4113_;
v_isShared_4117_ = v_isSharedCheck_4516_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_a_4114_);
lean_dec(v___x_4113_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4516_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
uint8_t v___x_4118_; 
v___x_4118_ = lean_unbox(v_a_4114_);
lean_dec(v_a_4114_);
if (v___x_4118_ == 0)
{
lean_object* v___x_4119_; 
lean_del_object(v___x_4116_);
lean_inc(v_goal_4054_);
v___x_4119_ = l_Lean_MVarId_getType(v_goal_4054_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4503_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4122_ = v___x_4119_;
v_isShared_4123_ = v_isSharedCheck_4503_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4119_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4503_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v_options_4271_; lean_object* v_inheritedTraceOptions_4272_; uint8_t v_hasTrace_4273_; lean_object* v___x_4274_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; 
v_options_4271_ = lean_ctor_get(v___y_4065_, 2);
v_inheritedTraceOptions_4272_ = lean_ctor_get(v___y_4065_, 13);
v_hasTrace_4273_ = lean_ctor_get_uint8(v_options_4271_, sizeof(void*)*1);
v___x_4274_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__4));
if (v_hasTrace_4273_ == 0)
{
v___y_4276_ = v___y_4056_;
v___y_4277_ = v___y_4057_;
v___y_4278_ = v___y_4058_;
v___y_4279_ = v___y_4059_;
v___y_4280_ = v___y_4060_;
v___y_4281_ = v___y_4061_;
v___y_4282_ = v___y_4062_;
v___y_4283_ = v___y_4063_;
v___y_4284_ = v___y_4064_;
v___y_4285_ = v___y_4065_;
v___y_4286_ = v___y_4066_;
goto v___jp_4275_;
}
else
{
lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4489_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4272_, v_options_4271_, v___x_4489_);
if (v___x_4490_ == 0)
{
v___y_4276_ = v___y_4056_;
v___y_4277_ = v___y_4057_;
v___y_4278_ = v___y_4058_;
v___y_4279_ = v___y_4059_;
v___y_4280_ = v___y_4060_;
v___y_4281_ = v___y_4061_;
v___y_4282_ = v___y_4062_;
v___y_4283_ = v___y_4063_;
v___y_4284_ = v___y_4064_;
v___y_4285_ = v___y_4065_;
v___y_4286_ = v___y_4066_;
goto v___jp_4275_;
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4491_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__7);
lean_inc(v_a_4120_);
v___x_4492_ = l_Lean_MessageData_ofExpr(v_a_4120_);
v___x_4493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4493_, 0, v___x_4491_);
lean_ctor_set(v___x_4493_, 1, v___x_4492_);
v___x_4494_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4274_, v___x_4493_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_dec_ref_known(v___x_4494_, 1);
v___y_4276_ = v___y_4056_;
v___y_4277_ = v___y_4057_;
v___y_4278_ = v___y_4058_;
v___y_4279_ = v___y_4059_;
v___y_4280_ = v___y_4060_;
v___y_4281_ = v___y_4061_;
v___y_4282_ = v___y_4062_;
v___y_4283_ = v___y_4063_;
v___y_4284_ = v___y_4064_;
v___y_4285_ = v___y_4065_;
v___y_4286_ = v___y_4066_;
goto v___jp_4275_;
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
v___jp_4124_:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4128_; 
v___x_4125_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_a_4120_);
v___x_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
if (v_isShared_4123_ == 0)
{
lean_ctor_set(v___x_4122_, 0, v___x_4126_);
v___x_4128_ = v___x_4122_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v___x_4126_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
v___jp_4130_:
{
lean_object* v___x_4144_; 
v___x_4144_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_4141_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v___x_4145_; 
lean_dec_ref_known(v___x_4144_, 1);
v___x_4145_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_applySpec(v___y_4137_, v_goal_4054_, v_a_4120_, v___y_4134_, v___y_4140_, v___y_4141_, v___y_4135_, v___y_4142_, v___y_4132_, v___y_4143_, v___y_4133_, v___y_4131_, v___y_4139_, v___y_4138_, v___y_4136_);
return v___x_4145_;
}
else
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4153_; 
lean_dec_ref(v___y_4137_);
lean_dec_ref(v___y_4134_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4146_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4148_ = v___x_4144_;
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4144_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4153_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
lean_object* v___x_4151_; 
if (v_isShared_4149_ == 0)
{
v___x_4151_ = v___x_4148_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_a_4146_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
v___jp_4154_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_dec_ref(v___y_4156_);
lean_dec_ref(v___y_4155_);
v___x_4170_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v___y_4157_);
v___x_4171_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v___y_4157_);
lean_inc_ref(v___x_4171_);
lean_inc_ref(v___x_4170_);
v___x_4172_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_matchesUntilPattern___redArg(v___x_4170_, v___x_4171_, v___y_4159_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4262_; 
v_a_4173_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4175_ = v___x_4172_;
v_isShared_4176_ = v_isSharedCheck_4262_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4172_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4262_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
uint8_t v___x_4177_; 
v___x_4177_ = lean_unbox(v_a_4173_);
lean_dec(v_a_4173_);
if (v___x_4177_ == 0)
{
lean_object* v___x_4178_; 
lean_del_object(v___x_4175_);
lean_dec_ref(v___x_4170_);
lean_inc_ref(v___y_4157_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4178_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpLet_x3f(v_goal_4054_, v_a_4120_, v___y_4157_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
if (lean_obj_tag(v_a_4179_) == 1)
{
lean_object* v_val_4180_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4180_ = lean_ctor_get(v_a_4179_, 0);
lean_inc(v_val_4180_);
lean_dec_ref_known(v_a_4179_, 1);
v___y_4090_ = v___y_4158_;
v_g_4091_ = v_val_4180_;
v___y_4092_ = v___y_4160_;
goto v___jp_4089_;
}
else
{
lean_object* v___x_4181_; 
lean_dec(v_a_4179_);
lean_inc_ref(v___y_4157_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4181_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpMatch_x3f(v_goal_4054_, v_a_4120_, v___y_4157_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4181_) == 0)
{
lean_object* v_a_4182_; 
v_a_4182_ = lean_ctor_get(v___x_4181_, 0);
lean_inc(v_a_4182_);
lean_dec_ref_known(v___x_4181_, 1);
if (lean_obj_tag(v_a_4182_) == 1)
{
lean_object* v_val_4183_; lean_object* v___x_4184_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4183_ = lean_ctor_get(v_a_4182_, 0);
lean_inc(v_val_4183_);
lean_dec_ref_known(v_a_4182_, 1);
v___x_4184_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_4160_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4192_; 
v_isSharedCheck_4192_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4192_ == 0)
{
lean_object* v_unused_4193_; 
v_unused_4193_ = lean_ctor_get(v___x_4184_, 0);
lean_dec(v_unused_4193_);
v___x_4186_ = v___x_4184_;
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
else
{
lean_dec(v___x_4184_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4192_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4188_; lean_object* v___x_4190_; 
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___y_4158_);
lean_ctor_set(v___x_4188_, 1, v_val_4183_);
if (v_isShared_4187_ == 0)
{
lean_ctor_set(v___x_4186_, 0, v___x_4188_);
v___x_4190_ = v___x_4186_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec(v_val_4183_);
lean_dec_ref(v___y_4158_);
v_a_4194_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4184_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4184_);
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
lean_object* v___x_4202_; 
lean_dec(v_a_4182_);
lean_inc_ref(v___y_4157_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4202_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpFVarZeta_x3f(v_goal_4054_, v_a_4120_, v___y_4157_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
if (lean_obj_tag(v_a_4203_) == 1)
{
lean_object* v_val_4204_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4204_ = lean_ctor_get(v_a_4203_, 0);
lean_inc(v_val_4204_);
lean_dec_ref_known(v_a_4203_, 1);
v___y_4090_ = v___y_4158_;
v_g_4091_ = v_val_4204_;
v___y_4092_ = v___y_4160_;
goto v___jp_4089_;
}
else
{
lean_object* v___x_4205_; 
lean_dec(v_a_4203_);
lean_inc_ref(v___y_4157_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4205_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_wpHeadReduce_x3f(v_goal_4054_, v_a_4120_, v___y_4157_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
if (lean_obj_tag(v_a_4206_) == 1)
{
lean_object* v_val_4207_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4207_ = lean_ctor_get(v_a_4206_, 0);
lean_inc(v_val_4207_);
lean_dec_ref_known(v_a_4206_, 1);
v___y_4090_ = v___y_4158_;
v_g_4091_ = v_val_4207_;
v___y_4092_ = v___y_4160_;
goto v___jp_4089_;
}
else
{
lean_object* v___x_4208_; uint8_t v___x_4209_; 
lean_dec(v_a_4206_);
v___x_4208_ = l_Lean_Expr_getAppFn(v___x_4171_);
v___x_4209_ = l_Lean_Expr_isConst(v___x_4208_);
if (v___x_4209_ == 0)
{
uint8_t v___x_4210_; 
v___x_4210_ = l_Lean_Expr_isFVar(v___x_4208_);
lean_dec_ref(v___x_4208_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v___x_4211_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__1);
v___x_4212_ = l_Lean_MessageData_ofExpr(v___x_4171_);
v___x_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__3);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f_spec__0___redArg(v___x_4215_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
else
{
lean_dec_ref(v___x_4171_);
v___y_4131_ = v___y_4166_;
v___y_4132_ = v___y_4163_;
v___y_4133_ = v___y_4165_;
v___y_4134_ = v___y_4157_;
v___y_4135_ = v___y_4161_;
v___y_4136_ = v___y_4169_;
v___y_4137_ = v___y_4158_;
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4159_;
v___y_4141_ = v___y_4160_;
v___y_4142_ = v___y_4162_;
v___y_4143_ = v___y_4164_;
goto v___jp_4130_;
}
}
else
{
lean_dec_ref(v___x_4208_);
lean_dec_ref(v___x_4171_);
v___y_4131_ = v___y_4166_;
v___y_4132_ = v___y_4163_;
v___y_4133_ = v___y_4165_;
v___y_4134_ = v___y_4157_;
v___y_4135_ = v___y_4161_;
v___y_4136_ = v___y_4169_;
v___y_4137_ = v___y_4158_;
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4167_;
v___y_4140_ = v___y_4159_;
v___y_4141_ = v___y_4160_;
v___y_4142_ = v___y_4162_;
v___y_4143_ = v___y_4164_;
goto v___jp_4130_;
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4225_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4205_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4205_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4233_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4202_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4202_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
}
else
{
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4241_ = lean_ctor_get(v___x_4181_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4181_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4181_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4181_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
}
}
else
{
lean_object* v_a_4249_; lean_object* v___x_4251_; uint8_t v_isShared_4252_; uint8_t v_isSharedCheck_4256_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4249_ = lean_ctor_get(v___x_4178_, 0);
v_isSharedCheck_4256_ = !lean_is_exclusive(v___x_4178_);
if (v_isSharedCheck_4256_ == 0)
{
v___x_4251_ = v___x_4178_;
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
else
{
lean_inc(v_a_4249_);
lean_dec(v___x_4178_);
v___x_4251_ = lean_box(0);
v_isShared_4252_ = v_isSharedCheck_4256_;
goto v_resetjp_4250_;
}
v_resetjp_4250_:
{
lean_object* v___x_4254_; 
if (v_isShared_4252_ == 0)
{
v___x_4254_ = v___x_4251_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4255_; 
v_reuseFailAlloc_4255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4255_, 0, v_a_4249_);
v___x_4254_ = v_reuseFailAlloc_4255_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
return v___x_4254_;
}
}
}
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4260_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v___x_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4170_);
v___x_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4257_);
if (v_isShared_4176_ == 0)
{
lean_ctor_set(v___x_4175_, 0, v___x_4258_);
v___x_4260_ = v___x_4175_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec_ref(v___x_4171_);
lean_dec_ref(v___x_4170_);
lean_dec_ref(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4263_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4172_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4172_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
v___jp_4275_:
{
lean_object* v___x_4287_; 
lean_inc(v_goal_4054_);
v___x_4287_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_forallIntro_x3f(v_goal_4054_, v_a_4120_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
lean_inc(v_a_4288_);
lean_dec_ref_known(v___x_4287_, 1);
if (lean_obj_tag(v_a_4288_) == 1)
{
lean_object* v_val_4289_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4289_ = lean_ctor_get(v_a_4288_, 0);
lean_inc(v_val_4289_);
lean_dec_ref_known(v_a_4288_, 1);
v_gs_4075_ = v_val_4289_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4290_; 
lean_dec(v_a_4288_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4290_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f(v_goal_4054_, v_a_4120_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
if (lean_obj_tag(v_a_4291_) == 1)
{
lean_object* v_val_4292_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4292_ = lean_ctor_get(v_a_4291_, 0);
lean_inc(v_val_4292_);
lean_dec_ref_known(v_a_4291_, 1);
v_g_4069_ = v_val_4292_;
goto v___jp_4068_;
}
else
{
lean_object* v___x_4293_; 
lean_dec(v_a_4291_);
lean_inc(v_goal_4054_);
v___x_4293_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_tripleUnfold_x3f(v_goal_4054_, v_a_4120_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
if (lean_obj_tag(v_a_4294_) == 1)
{
lean_object* v_val_4295_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4295_ = lean_ctor_get(v_a_4294_, 0);
lean_inc(v_val_4295_);
lean_dec_ref_known(v_a_4294_, 1);
v_g_4069_ = v_val_4295_;
goto v___jp_4068_;
}
else
{
lean_object* v___x_4296_; 
lean_dec(v_a_4294_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4296_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f(v_goal_4054_, v_a_4120_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
lean_inc(v_a_4297_);
lean_dec_ref_known(v___x_4296_, 1);
if (lean_obj_tag(v_a_4297_) == 1)
{
lean_object* v_val_4298_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4298_ = lean_ctor_get(v_a_4297_, 0);
lean_inc(v_val_4298_);
lean_dec_ref_known(v_a_4297_, 1);
v_g_4069_ = v_val_4298_;
goto v___jp_4068_;
}
else
{
lean_object* v___x_4299_; 
lean_dec(v_a_4297_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
lean_inc_ref(v_scope_4055_);
v___x_4299_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHypBare_x3f(v_scope_4055_, v_goal_4054_, v_a_4120_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
if (lean_obj_tag(v_a_4300_) == 1)
{
lean_object* v_val_4301_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4301_ = lean_ctor_get(v_a_4300_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v_a_4300_, 1);
v_gs_4075_ = v_val_4301_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4302_; uint8_t v___x_4303_; 
lean_dec(v_a_4300_);
lean_inc(v_a_4120_);
v___x_4302_ = l_Lean_Expr_cleanupAnnotations(v_a_4120_);
v___x_4303_ = l_Lean_Expr_isApp(v___x_4302_);
if (v___x_4303_ == 0)
{
lean_dec_ref(v___x_4302_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
goto v___jp_4124_;
}
else
{
lean_object* v_arg_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v_arg_4304_ = lean_ctor_get(v___x_4302_, 1);
lean_inc_ref(v_arg_4304_);
v___x_4305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4302_);
v___x_4306_ = l_Lean_Expr_isApp(v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec_ref(v___x_4305_);
lean_dec_ref(v_arg_4304_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
goto v___jp_4124_;
}
else
{
lean_object* v_arg_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_arg_4307_ = lean_ctor_get(v___x_4305_, 1);
lean_inc_ref(v_arg_4307_);
v___x_4308_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4305_);
v___x_4309_ = l_Lean_Expr_isApp(v___x_4308_);
if (v___x_4309_ == 0)
{
lean_dec_ref(v___x_4308_);
lean_dec_ref(v_arg_4307_);
lean_dec_ref(v_arg_4304_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
goto v___jp_4124_;
}
else
{
lean_object* v_arg_4310_; lean_object* v___x_4311_; uint8_t v___x_4312_; 
v_arg_4310_ = lean_ctor_get(v___x_4308_, 1);
lean_inc_ref(v_arg_4310_);
v___x_4311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4308_);
v___x_4312_ = l_Lean_Expr_isApp(v___x_4311_);
if (v___x_4312_ == 0)
{
lean_dec_ref(v___x_4311_);
lean_dec_ref(v_arg_4310_);
lean_dec_ref(v_arg_4307_);
lean_dec_ref(v_arg_4304_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
goto v___jp_4124_;
}
else
{
lean_object* v_arg_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; 
v_arg_4313_ = lean_ctor_get(v___x_4311_, 1);
lean_inc_ref(v_arg_4313_);
v___x_4314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4311_);
v___x_4315_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_bareWPToLe_x3f___closed__10));
v___x_4316_ = l_Lean_Expr_isConstOf(v___x_4314_, v___x_4315_);
lean_dec_ref(v___x_4314_);
if (v___x_4316_ == 0)
{
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec_ref(v_arg_4307_);
lean_dec_ref(v_arg_4304_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
goto v___jp_4124_;
}
else
{
lean_object* v___x_4317_; 
lean_del_object(v___x_4122_);
v___x_4317_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_4307_, v___y_4284_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
v___x_4319_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_4304_, v___y_4284_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
lean_inc(v_goal_4054_);
v___x_4321_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_rfl_x3f___redArg(v_goal_4054_, v___y_4276_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
if (lean_obj_tag(v_a_4322_) == 1)
{
lean_object* v_val_4323_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4323_ = lean_ctor_get(v_a_4322_, 0);
lean_inc(v_val_4323_);
lean_dec_ref_known(v_a_4322_, 1);
v_gs_4075_ = v_val_4323_;
goto v___jp_4074_;
}
else
{
lean_object* v___x_4324_; 
lean_dec(v_a_4322_);
lean_inc(v_a_4120_);
lean_inc(v_a_4318_);
lean_inc(v_goal_4054_);
lean_inc_ref(v_scope_4055_);
v___x_4324_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_normalizePre_x3f(v_scope_4055_, v_goal_4054_, v_arg_4313_, v_a_4318_, v_a_4120_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4416_; 
v_a_4325_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4327_ = v___x_4324_;
v_isShared_4328_ = v_isSharedCheck_4416_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4324_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4416_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
if (lean_obj_tag(v_a_4325_) == 1)
{
lean_object* v_val_4329_; lean_object* v_fst_4330_; lean_object* v_snd_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4341_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_val_4329_ = lean_ctor_get(v_a_4325_, 0);
lean_inc(v_val_4329_);
lean_dec_ref_known(v_a_4325_, 1);
v_fst_4330_ = lean_ctor_get(v_val_4329_, 0);
v_snd_4331_ = lean_ctor_get(v_val_4329_, 1);
v_isSharedCheck_4341_ = !lean_is_exclusive(v_val_4329_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4333_ = v_val_4329_;
v_isShared_4334_ = v_isSharedCheck_4341_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_snd_4331_);
lean_inc(v_fst_4330_);
lean_dec(v_val_4329_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4341_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_fst_4330_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_snd_4331_);
v___x_4336_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
lean_object* v___x_4338_; 
if (v_isShared_4328_ == 0)
{
lean_ctor_set(v___x_4327_, 0, v___x_4336_);
v___x_4338_ = v___x_4327_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v___x_4336_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
else
{
lean_object* v___x_4342_; 
lean_del_object(v___x_4327_);
lean_dec(v_a_4325_);
lean_inc(v_goal_4054_);
v___x_4342_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_4055_, v_goal_4054_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4344_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4343_);
lean_dec_ref_known(v___x_4342_, 1);
lean_inc(v_a_4320_);
lean_inc(v_a_4318_);
lean_inc_ref(v_arg_4313_);
lean_inc(v_a_4120_);
lean_inc(v_goal_4054_);
v___x_4344_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceEPostHead_x3f(v_goal_4054_, v_a_4120_, v_arg_4313_, v_arg_4310_, v_a_4318_, v_a_4320_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4344_) == 0)
{
lean_object* v_a_4345_; lean_object* v___x_4347_; uint8_t v_isShared_4348_; uint8_t v_isSharedCheck_4399_; 
v_a_4345_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4347_ = v___x_4344_;
v_isShared_4348_ = v_isSharedCheck_4399_;
goto v_resetjp_4346_;
}
else
{
lean_inc(v_a_4345_);
lean_dec(v___x_4344_);
v___x_4347_ = lean_box(0);
v_isShared_4348_ = v_isSharedCheck_4399_;
goto v_resetjp_4346_;
}
v_resetjp_4346_:
{
if (lean_obj_tag(v_a_4345_) == 1)
{
lean_object* v_val_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4354_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4349_ = lean_ctor_get(v_a_4345_, 0);
lean_inc(v_val_4349_);
lean_dec_ref_known(v_a_4345_, 1);
v___x_4350_ = lean_box(0);
v___x_4351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4351_, 0, v_val_4349_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v_a_4343_);
lean_ctor_set(v___x_4352_, 1, v___x_4351_);
if (v_isShared_4348_ == 0)
{
lean_ctor_set(v___x_4347_, 0, v___x_4352_);
v___x_4354_ = v___x_4347_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v___x_4352_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
else
{
lean_object* v___x_4356_; 
lean_del_object(v___x_4347_);
lean_dec(v_a_4345_);
lean_inc(v_a_4320_);
lean_inc(v_goal_4054_);
v___x_4356_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_splitLatticeOp_x3f(v_goal_4054_, v_a_4320_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
if (lean_obj_tag(v_a_4357_) == 1)
{
lean_object* v_val_4358_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4358_ = lean_ctor_get(v_a_4357_, 0);
lean_inc(v_val_4358_);
lean_dec_ref_known(v_a_4357_, 1);
v___y_4085_ = v_a_4343_;
v_gs_4086_ = v_val_4358_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4359_; 
lean_dec(v_a_4357_);
lean_inc(v_a_4320_);
lean_inc(v_a_4318_);
lean_inc(v_goal_4054_);
lean_inc(v_a_4343_);
v___x_4359_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f(v_a_4343_, v_goal_4054_, v_arg_4313_, v_a_4318_, v_a_4320_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
lean_dec_ref(v_arg_4313_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
if (lean_obj_tag(v_a_4360_) == 1)
{
lean_object* v_val_4361_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_val_4361_ = lean_ctor_get(v_a_4360_, 0);
lean_inc(v_val_4361_);
lean_dec_ref_known(v_a_4360_, 1);
v___y_4085_ = v_a_4343_;
v_gs_4086_ = v_val_4361_;
goto v___jp_4084_;
}
else
{
lean_object* v___x_4362_; 
lean_dec(v_a_4360_);
lean_inc(v_a_4320_);
v___x_4362_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_getWPInfo_x3f(v_a_4320_);
if (lean_obj_tag(v___x_4362_) == 1)
{
lean_object* v_options_4363_; uint8_t v_hasTrace_4364_; 
v_options_4363_ = lean_ctor_get(v___y_4285_, 2);
v_hasTrace_4364_ = lean_ctor_get_uint8(v_options_4363_, sizeof(void*)*1);
if (v_hasTrace_4364_ == 0)
{
lean_object* v_val_4365_; 
v_val_4365_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_val_4365_);
lean_dec_ref_known(v___x_4362_, 1);
v___y_4155_ = v_a_4318_;
v___y_4156_ = v_a_4320_;
v___y_4157_ = v_val_4365_;
v___y_4158_ = v_a_4343_;
v___y_4159_ = v___y_4276_;
v___y_4160_ = v___y_4277_;
v___y_4161_ = v___y_4278_;
v___y_4162_ = v___y_4279_;
v___y_4163_ = v___y_4280_;
v___y_4164_ = v___y_4281_;
v___y_4165_ = v___y_4282_;
v___y_4166_ = v___y_4283_;
v___y_4167_ = v___y_4284_;
v___y_4168_ = v___y_4285_;
v___y_4169_ = v___y_4286_;
goto v___jp_4154_;
}
else
{
lean_object* v_val_4366_; lean_object* v_inheritedTraceOptions_4367_; lean_object* v___x_4368_; uint8_t v___x_4369_; 
v_val_4366_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_val_4366_);
lean_dec_ref_known(v___x_4362_, 1);
v_inheritedTraceOptions_4367_ = lean_ctor_get(v___y_4285_, 13);
v___x_4368_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f___closed__7);
v___x_4369_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4367_, v_options_4363_, v___x_4368_);
if (v___x_4369_ == 0)
{
v___y_4155_ = v_a_4318_;
v___y_4156_ = v_a_4320_;
v___y_4157_ = v_val_4366_;
v___y_4158_ = v_a_4343_;
v___y_4159_ = v___y_4276_;
v___y_4160_ = v___y_4277_;
v___y_4161_ = v___y_4278_;
v___y_4162_ = v___y_4279_;
v___y_4163_ = v___y_4280_;
v___y_4164_ = v___y_4281_;
v___y_4165_ = v___y_4282_;
v___y_4166_ = v___y_4283_;
v___y_4167_ = v___y_4284_;
v___y_4168_ = v___y_4285_;
v___y_4169_ = v___y_4286_;
goto v___jp_4154_;
}
else
{
lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4370_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5, &l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__5);
v___x_4371_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_val_4366_);
v___x_4372_ = l_Lean_MessageData_ofExpr(v___x_4371_);
v___x_4373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4373_, 0, v___x_4370_);
lean_ctor_set(v___x_4373_, 1, v___x_4372_);
v___x_4374_ = l_Lean_addTrace___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_targetLetIntro_x3f_spec__0___redArg(v___x_4274_, v___x_4373_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_dec_ref_known(v___x_4374_, 1);
v___y_4155_ = v_a_4318_;
v___y_4156_ = v_a_4320_;
v___y_4157_ = v_val_4366_;
v___y_4158_ = v_a_4343_;
v___y_4159_ = v___y_4276_;
v___y_4160_ = v___y_4277_;
v___y_4161_ = v___y_4278_;
v___y_4162_ = v___y_4279_;
v___y_4163_ = v___y_4280_;
v___y_4164_ = v___y_4281_;
v___y_4165_ = v___y_4282_;
v___y_4166_ = v___y_4283_;
v___y_4167_ = v___y_4284_;
v___y_4168_ = v___y_4285_;
v___y_4169_ = v___y_4286_;
goto v___jp_4154_;
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v_val_4366_);
lean_dec(v_a_4343_);
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4374_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4374_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
}
else
{
lean_dec(v___x_4362_);
lean_dec(v_a_4343_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v___y_4079_ = v_a_4318_;
v___y_4080_ = v_a_4320_;
goto v___jp_4078_;
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec(v_a_4343_);
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4383_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4359_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4359_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_dec(v_a_4343_);
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4391_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4356_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4356_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_dec(v_a_4343_);
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4400_ = lean_ctor_get(v___x_4344_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4344_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4344_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec(v_a_4120_);
lean_dec(v_goal_4054_);
v_a_4408_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4342_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4342_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4417_ = lean_ctor_get(v___x_4324_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4324_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4324_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4324_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4425_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4321_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4321_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_a_4318_);
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4433_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4319_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4319_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec_ref(v_arg_4313_);
lean_dec_ref(v_arg_4310_);
lean_dec_ref(v_arg_4304_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4441_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4317_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4317_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
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
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4449_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4299_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4299_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4457_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4296_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4296_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4465_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4293_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4293_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4473_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4290_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4290_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_del_object(v___x_4122_);
lean_dec(v_a_4120_);
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4481_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4287_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4287_);
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
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4504_ = lean_ctor_get(v___x_4119_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4119_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4119_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4119_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4514_; 
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v___x_4512_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___closed__8));
if (v_isShared_4117_ == 0)
{
lean_ctor_set(v___x_4116_, 0, v___x_4512_);
v___x_4514_ = v___x_4116_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec_ref(v_scope_4055_);
lean_dec(v_goal_4054_);
v_a_4517_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4113_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4113_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
v___jp_4068_:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4070_ = lean_box(0);
v___x_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4071_, 0, v_g_4069_);
lean_ctor_set(v___x_4071_, 1, v___x_4070_);
v___x_4072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4072_, 0, v_scope_4055_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v___x_4072_);
return v___x_4073_;
}
v___jp_4074_:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v_scope_4055_);
lean_ctor_set(v___x_4076_, 1, v_gs_4075_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
v___jp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___y_4079_);
lean_ctor_set(v___x_4081_, 1, v___y_4080_);
v___x_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
v___jp_4084_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___y_4085_);
lean_ctor_set(v___x_4087_, 1, v_gs_4086_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
v___jp_4089_:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v___y_4092_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v___x_4095_; uint8_t v_isShared_4096_; uint8_t v_isSharedCheck_4103_; 
v_isSharedCheck_4103_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4103_ == 0)
{
lean_object* v_unused_4104_; 
v_unused_4104_ = lean_ctor_get(v___x_4093_, 0);
lean_dec(v_unused_4104_);
v___x_4095_ = v___x_4093_;
v_isShared_4096_ = v_isSharedCheck_4103_;
goto v_resetjp_4094_;
}
else
{
lean_dec(v___x_4093_);
v___x_4095_ = lean_box(0);
v_isShared_4096_ = v_isSharedCheck_4103_;
goto v_resetjp_4094_;
}
v_resetjp_4094_:
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4101_; 
v___x_4097_ = lean_box(0);
v___x_4098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4098_, 0, v_g_4091_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___y_4090_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
if (v_isShared_4096_ == 0)
{
lean_ctor_set(v___x_4095_, 0, v___x_4099_);
v___x_4101_ = v___x_4095_;
goto v_reusejp_4100_;
}
else
{
lean_object* v_reuseFailAlloc_4102_; 
v_reuseFailAlloc_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___x_4099_);
v___x_4101_ = v_reuseFailAlloc_4102_;
goto v_reusejp_4100_;
}
v_reusejp_4100_:
{
return v___x_4101_;
}
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_g_4091_);
lean_dec_ref(v___y_4090_);
v_a_4105_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4093_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4093_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed(lean_object* v_goal_4525_, lean_object* v_scope_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0(v_goal_4525_, v_scope_4526_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(lean_object* v_scope_4540_, lean_object* v_goal_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_, lean_object* v_a_4547_, lean_object* v_a_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v___f_4554_; lean_object* v___x_4555_; 
lean_inc(v_goal_4541_);
v___f_4554_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___lam__0___boxed), 14, 2);
lean_closure_set(v___f_4554_, 0, v_goal_4541_);
lean_closure_set(v___f_4554_, 1, v_scope_4540_);
v___x_4555_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Solve_0__Lean_Elab_Tactic_Do_Internal_VCGen_liftedHyp_x3f_spec__0___redArg(v_goal_4541_, v___f_4554_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
return v___x_4555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_solve___boxed(lean_object* v_scope_4556_, lean_object* v_goal_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_solve(v_scope_4556_, v_goal_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
lean_dec(v_a_4562_);
lean_dec_ref(v_a_4561_);
lean_dec(v_a_4560_);
lean_dec(v_a_4559_);
lean_dec_ref(v_a_4558_);
return v_res_4570_;
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
