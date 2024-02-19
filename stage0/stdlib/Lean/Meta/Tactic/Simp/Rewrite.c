// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Rewrite
// Imports: Init Lean.Meta.ACLt Lean.Meta.Match.MatchEqsExt Lean.Meta.AppBuilder Lean.Meta.SynthInstance Lean.Meta.Tactic.UnifyEq Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.LinearArith.Simp Lean.Meta.Tactic.Simp.Simproc
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_postDefault___lambda__1___closed__2;
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__13;
extern lean_object* l_Lean_profiler;
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
static lean_object* l_Lean_Meta_Simp_simpCtorEq___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1;
static lean_object* l_Lean_Meta_Simp_mkDefaultMethods___closed__1;
lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__2;
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2;
uint32_t l_UInt32_ofNatTruncate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeUsingAssumption_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods___boxed(lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__3;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Linear_isLinearCnstr(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis___boxed(lean_object*);
double l_Lean_trace_profiler_threshold_getSecs(lean_object*);
static lean_object* l_Lean_Meta_Simp_simpGround___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_isLemma___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_seval___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t lean_float_decLt(double, double);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13;
static lean_object* l_Lean_Meta_Simp_preSEval___lambda__1___closed__1;
lean_object* l_Lean_Meta_Simp_getSimprocs___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5;
lean_object* l_Lean_Meta_getSimpCongrTheorems___rarg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_simprocs;
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5;
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5;
static lean_object* l_Lean_Meta_Simp_dischargeGround___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpCtorEq___closed__6;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7;
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__5;
extern lean_object* l_Lean_Meta_sevalSimpExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_sevalGround___lambda__2___closed__1;
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpCtorEq___closed__4;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_simpGround___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_postDefault___lambda__1___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3;
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__3;
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__1;
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_sevalGround___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
static lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__3;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11;
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__1;
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1;
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5;
lean_object* lean_io_mono_nanos_now(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7;
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
static lean_object* l_Lean_Meta_Simp_simpCtorEq___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1;
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_simpGround___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12;
uint8_t l_Lean_Expr_isArrow(lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Linear_parentIsTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6;
static lean_object* l_Lean_Meta_Simp_postDefault___lambda__3___closed__1;
lean_object* l_Lean_Meta_Linear_Nat_simpCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpGround___lambda__1___closed__2;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7;
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Simp_simpCtorEq___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Linear_isLinearTerm(lean_object*);
static lean_object* l_Lean_Meta_Simp_postSEval___lambda__1___closed__1;
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Linear_Nat_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_postDefault___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Meta_Simp_discharge_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__1;
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15;
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_Meta_Simp_mkSEvalContext___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_postDefault___lambda__2___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ACLt_main_lt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___boxed(lean_object**);
static lean_object* l_Lean_Meta_Simp_preDefault___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3;
static lean_object* l_Lean_Meta_Simp_preSEval___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3___closed__1;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2;
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__14;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___rarg(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object*);
lean_object* l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSEvalContext___closed__2;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpCtorEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3;
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpCtorEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1(lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__1;
static lean_object* l_Lean_Meta_Simp_postSEval___lambda__1___closed__2;
extern lean_object* l_Lean_trace_profiler;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2;
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeGround___closed__2;
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__16;
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1;
static lean_object* l_Lean_Meta_Simp_mkDefaultMethods___closed__2;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__2;
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__2;
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkSEvalContext___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_postSEval___closed__1;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1;
static lean_object* l_Lean_Meta_Simp_postSEval___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__1;
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5;
static lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__8;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown constant '", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = lean_environment_find(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_1, x_16);
x_18 = l_Lean_MessageData_ofExpr(x_17);
x_19 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_1);
x_28 = lean_environment_find(x_27, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_1, x_29);
x_31 = l_Lean_MessageData_ofExpr(x_30);
x_32 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_26);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_ConstantInfo_levelParams(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_14);
x_16 = l_Lean_Expr_const___override(x_1, x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = l_Lean_ConstantInfo_levelParams(x_17);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_19, x_20);
x_22 = l_Lean_Expr_const___override(x_1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("↓ ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("↓ ← ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("← ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
x_13 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
if (x_11 == 0)
{
if (x_12 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_13, 0, x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = l_Lean_MessageData_ofExpr(x_21);
x_24 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = l_Lean_MessageData_ofExpr(x_30);
x_32 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_13, 0, x_35);
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = l_Lean_MessageData_ofExpr(x_36);
x_39 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
if (x_12 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = l_Lean_MessageData_ofExpr(x_45);
lean_ctor_set(x_13, 0, x_46);
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_13, 0);
x_48 = lean_ctor_get(x_13, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_13);
x_49 = l_Lean_MessageData_ofExpr(x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = l_Lean_MessageData_ofExpr(x_52);
x_54 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_13, 0, x_57);
return x_13;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_13, 0);
x_59 = lean_ctor_get(x_13, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_13);
x_60 = l_Lean_MessageData_ofExpr(x_58);
x_61 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_13);
if (x_66 == 0)
{
return x_13;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_13, 0);
x_68 = lean_ctor_get(x_13, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_13);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
case 1:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_Expr_fvar___override(x_70);
x_72 = l_Lean_MessageData_ofExpr(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
return x_73;
}
case 2:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_75 = l_Lean_MessageData_ofSyntax(x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_9);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_1, 0);
lean_inc(x_77);
lean_dec(x_1);
x_78 = l_Lean_MessageData_ofName(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_9);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("discharge", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to synthesize instance", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to assign instance", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nsythesized value", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nis not definitionally equal to", 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_13 = l_Lean_Meta_trySynthInstance(x_3, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 5);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_24 = 3;
lean_ctor_set_uint8(x_15, 9, x_24);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_18);
lean_ctor_set(x_25, 2, x_19);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_2);
x_26 = l_Lean_Meta_isExprDefEq(x_2, x_17, x_25, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_31 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
x_35 = lean_unbox(x_32);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_apply_9(x_34, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
x_43 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_indentExpr(x_3);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_indentExpr(x_17);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_indentExpr(x_2);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_41);
x_56 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_30, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_apply_9(x_34, x_57, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_38);
if (x_60 == 0)
{
return x_38;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_38, 0);
x_62 = lean_ctor_get(x_38, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_38);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
lean_dec(x_65);
x_66 = 1;
x_67 = lean_box(x_66);
lean_ctor_set(x_26, 0, x_67);
return x_26;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_26, 1);
lean_inc(x_68);
lean_dec(x_26);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_26);
if (x_72 == 0)
{
return x_26;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_26, 0);
x_74 = lean_ctor_get(x_26, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_26);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get_uint8(x_15, 0);
x_77 = lean_ctor_get_uint8(x_15, 1);
x_78 = lean_ctor_get_uint8(x_15, 2);
x_79 = lean_ctor_get_uint8(x_15, 3);
x_80 = lean_ctor_get_uint8(x_15, 4);
x_81 = lean_ctor_get_uint8(x_15, 5);
x_82 = lean_ctor_get_uint8(x_15, 6);
x_83 = lean_ctor_get_uint8(x_15, 7);
x_84 = lean_ctor_get_uint8(x_15, 8);
x_85 = lean_ctor_get_uint8(x_15, 10);
x_86 = lean_ctor_get_uint8(x_15, 11);
lean_dec(x_15);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_88, 0, x_76);
lean_ctor_set_uint8(x_88, 1, x_77);
lean_ctor_set_uint8(x_88, 2, x_78);
lean_ctor_set_uint8(x_88, 3, x_79);
lean_ctor_set_uint8(x_88, 4, x_80);
lean_ctor_set_uint8(x_88, 5, x_81);
lean_ctor_set_uint8(x_88, 6, x_82);
lean_ctor_set_uint8(x_88, 7, x_83);
lean_ctor_set_uint8(x_88, 8, x_84);
lean_ctor_set_uint8(x_88, 9, x_87);
lean_ctor_set_uint8(x_88, 10, x_85);
lean_ctor_set_uint8(x_88, 11, x_86);
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_18);
lean_ctor_set(x_89, 2, x_19);
lean_ctor_set(x_89, 3, x_20);
lean_ctor_set(x_89, 4, x_21);
lean_ctor_set(x_89, 5, x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
lean_inc(x_2);
x_90 = l_Lean_Meta_isExprDefEq(x_2, x_17, x_89, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_95 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_94, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
x_99 = lean_unbox(x_96);
lean_dec(x_96);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = lean_box(0);
x_101 = lean_apply_9(x_98, x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_97);
return x_101;
}
else
{
lean_object* x_102; 
x_102 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_97);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
x_107 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_indentExpr(x_3);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_indentExpr(x_17);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_indentExpr(x_2);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_105);
x_120 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_94, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_104);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_apply_9(x_98, x_121, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_ctor_get(x_102, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_102, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_126 = x_102;
} else {
 lean_dec_ref(x_102);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_90, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_129 = x_90;
} else {
 lean_dec_ref(x_90);
 x_129 = lean_box(0);
}
x_130 = 1;
x_131 = lean_box(x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_128);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = lean_ctor_get(x_90, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_90, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_135 = x_90;
} else {
 lean_dec_ref(x_90);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_14);
lean_dec(x_2);
x_137 = lean_ctor_get(x_13, 1);
lean_inc(x_137);
lean_dec(x_13);
x_138 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_139 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_138, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_137);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
x_143 = lean_unbox(x_140);
lean_dec(x_140);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_3);
lean_dec(x_1);
x_144 = lean_box(0);
x_145 = lean_apply_9(x_142, x_144, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_141);
return x_145;
}
else
{
lean_object* x_146; 
x_146 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_141);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_151 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_indentExpr(x_3);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_149);
x_156 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_138, x_155, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_148);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_apply_9(x_142, x_157, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_158);
return x_159;
}
else
{
uint8_t x_160; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = !lean_is_exclusive(x_146);
if (x_160 == 0)
{
return x_146;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_146, 0);
x_162 = lean_ctor_get(x_146, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_146);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_13);
if (x_164 == 0)
{
return x_13;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_13, 0);
x_166 = lean_ctor_get(x_13, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_13);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasMVar(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_st_ref_get(x_6, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVarsCore(x_15, x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_take(x_6, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_18);
x_24 = lean_st_ref_set(x_6, x_20, x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_17);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_20, 1);
x_30 = lean_ctor_get(x_20, 2);
x_31 = lean_ctor_get(x_20, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_6, x_32, x_21);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_17);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_13, 2);
lean_dec(x_16);
lean_ctor_set(x_13, 2, x_1);
x_17 = lean_st_ref_set(x_6, x_13, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_2);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
x_30 = lean_ctor_get(x_13, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_1);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_6, x_31, x_14);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to discharge hypotheses", 32);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to assign proof", 24);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_dec(x_6);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_Meta_isProp(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_st_ref_get(x_9, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 2);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_31 = l_Lean_Meta_Simp_discharge_x3f(x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_2);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_35 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_4);
lean_dec(x_1);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_30, x_3, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
x_42 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_indentExpr(x_1);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_34, x_51, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_30, x_3, x_53, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_54);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_53);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
return x_42;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_31, 1);
lean_inc(x_60);
lean_dec(x_31);
x_61 = lean_ctor_get(x_32, 0);
lean_inc(x_61);
lean_dec(x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_62 = l_Lean_Meta_isExprDefEq(x_5, x_61, x_10, x_11, x_12, x_13, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_2);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_67 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_65);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
lean_dec(x_1);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_box(0);
x_72 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_30, x_3, x_71, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_70);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
x_74 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
x_79 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_indentExpr(x_1);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
x_84 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_66, x_83, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_76);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_30, x_3, x_85, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_86);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_85);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_74);
if (x_88 == 0)
{
return x_74;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_74, 0);
x_90 = lean_ctor_get(x_74, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_74);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_62);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_62, 0);
lean_dec(x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_2);
lean_ctor_set(x_94, 1, x_3);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_62, 0, x_95);
return x_62;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_62, 1);
lean_inc(x_96);
lean_dec(x_62);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_2);
lean_ctor_set(x_97, 1, x_3);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_62);
if (x_100 == 0)
{
return x_62;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_62, 0);
x_102 = lean_ctor_get(x_62, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_62);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_31);
if (x_104 == 0)
{
return x_31;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_31, 0);
x_106 = lean_ctor_get(x_31, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_31);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_15);
if (x_108 == 0)
{
return x_15;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_15, 0);
x_110 = lean_ctor_get(x_15, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_15);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_27; 
x_17 = lean_array_uget(x_3, x_5);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_6, 1);
x_29 = lean_ctor_get(x_6, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_28, 2);
lean_inc(x_32);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_6);
x_18 = x_34;
x_19 = x_14;
goto block_26;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_28, 2);
lean_dec(x_36);
x_37 = lean_ctor_get(x_28, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_array_fget(x_30, x_31);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_31, x_41);
lean_dec(x_31);
lean_ctor_set(x_28, 1, x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_43 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_BinderInfo_isInstImplicit(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_inc(x_17);
x_47 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Expr_isMVar(x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_44);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_6);
x_18 = x_51;
x_19 = x_49;
goto block_26;
}
else
{
lean_object* x_52; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_44);
x_52 = l_Lean_Meta_isClass_x3f(x_44, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_free_object(x_6);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_2);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_44, x_2, x_28, x_1, x_17, x_55, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_18 = x_57;
x_19 = x_58;
goto block_26;
}
else
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
return x_56;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
x_63 = lean_ctor_get(x_52, 1);
lean_inc(x_63);
lean_dec(x_52);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_44);
lean_inc(x_17);
lean_inc(x_1);
x_64 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_6);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_2);
x_69 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_44, x_2, x_28, x_1, x_17, x_68, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_18 = x_70;
x_19 = x_71;
goto block_26;
}
else
{
uint8_t x_72; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
return x_69;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_69);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_44);
lean_dec(x_17);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_dec(x_64);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_6);
x_18 = x_77;
x_19 = x_76;
goto block_26;
}
}
else
{
uint8_t x_78; 
lean_dec(x_44);
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_64);
if (x_78 == 0)
{
return x_64;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_64, 0);
x_80 = lean_ctor_get(x_64, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_64);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_44);
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_52);
if (x_82 == 0)
{
return x_52;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_52, 0);
x_84 = lean_ctor_get(x_52, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_52);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
lean_object* x_86; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_86 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_6, 0, x_90);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_6);
x_18 = x_91;
x_19 = x_89;
goto block_26;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
lean_dec(x_86);
lean_inc(x_2);
lean_ctor_set(x_6, 0, x_2);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_6);
x_18 = x_93;
x_19 = x_92;
goto block_26;
}
}
else
{
uint8_t x_94; 
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_28);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_43);
if (x_98 == 0)
{
return x_43;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_43, 0);
x_100 = lean_ctor_get(x_43, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_43);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_28);
x_102 = lean_array_fget(x_30, x_31);
x_103 = lean_unbox(x_102);
lean_dec(x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_31, x_104);
lean_dec(x_31);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_30);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_32);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_107 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_BinderInfo_isInstImplicit(x_103);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_inc(x_17);
x_111 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_109);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l_Lean_Expr_isMVar(x_112);
lean_dec(x_112);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_108);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_106);
lean_ctor_set(x_6, 0, x_2);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_6);
x_18 = x_115;
x_19 = x_113;
goto block_26;
}
else
{
lean_object* x_116; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_108);
x_116 = l_Lean_Meta_isClass_x3f(x_108, x_10, x_11, x_12, x_13, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_free_object(x_6);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_2);
x_120 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_108, x_2, x_106, x_1, x_17, x_119, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_118);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_18 = x_121;
x_19 = x_122;
goto block_26;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_125 = x_120;
} else {
 lean_dec_ref(x_120);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_117);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_dec(x_116);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_108);
lean_inc(x_17);
lean_inc(x_1);
x_128 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_108, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_6);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_2);
x_133 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_108, x_2, x_106, x_1, x_17, x_132, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_18 = x_134;
x_19 = x_135;
goto block_26;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_138 = x_133;
} else {
 lean_dec_ref(x_133);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_108);
lean_dec(x_17);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
lean_dec(x_128);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_106);
lean_ctor_set(x_6, 0, x_2);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_6);
x_18 = x_141;
x_19 = x_140;
goto block_26;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_108);
lean_dec(x_106);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_ctor_get(x_128, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_128, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_144 = x_128;
} else {
 lean_dec_ref(x_128);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_108);
lean_dec(x_106);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_146 = lean_ctor_get(x_116, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_116, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_148 = x_116;
} else {
 lean_dec_ref(x_116);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
else
{
lean_object* x_150; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_150 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_108, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_109);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_6, 1, x_106);
lean_ctor_set(x_6, 0, x_154);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_6);
x_18 = x_155;
x_19 = x_153;
goto block_26;
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
lean_dec(x_150);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_106);
lean_ctor_set(x_6, 0, x_2);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_6);
x_18 = x_157;
x_19 = x_156;
goto block_26;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_106);
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_160 = x_150;
} else {
 lean_dec_ref(x_150);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_106);
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_107, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_107, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_164 = x_107;
} else {
 lean_dec_ref(x_107);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_6, 1);
lean_inc(x_166);
lean_dec(x_6);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_166, 2);
lean_inc(x_169);
x_170 = lean_nat_dec_lt(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_17);
lean_inc(x_2);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_2);
lean_ctor_set(x_171, 1, x_166);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_171);
x_18 = x_172;
x_19 = x_14;
goto block_26;
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 x_173 = x_166;
} else {
 lean_dec_ref(x_166);
 x_173 = lean_box(0);
}
x_174 = lean_array_fget(x_167, x_168);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_nat_add(x_168, x_176);
lean_dec(x_168);
if (lean_is_scalar(x_173)) {
 x_178 = lean_alloc_ctor(0, 3, 0);
} else {
 x_178 = x_173;
}
lean_ctor_set(x_178, 0, x_167);
lean_ctor_set(x_178, 1, x_177);
lean_ctor_set(x_178, 2, x_169);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
x_179 = lean_infer_type(x_17, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_BinderInfo_isInstImplicit(x_175);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_inc(x_17);
x_183 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_181);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Lean_Expr_isMVar(x_184);
lean_dec(x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_180);
lean_dec(x_17);
lean_inc(x_2);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_2);
lean_ctor_set(x_187, 1, x_178);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_18 = x_188;
x_19 = x_185;
goto block_26;
}
else
{
lean_object* x_189; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_180);
x_189 = l_Lean_Meta_isClass_x3f(x_180, x_10, x_11, x_12, x_13, x_185);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_2);
x_193 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_180, x_2, x_178, x_1, x_17, x_192, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_18 = x_194;
x_19 = x_195;
goto block_26;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_198 = x_193;
} else {
 lean_dec_ref(x_193);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_190);
x_200 = lean_ctor_get(x_189, 1);
lean_inc(x_200);
lean_dec(x_189);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_180);
lean_inc(x_17);
lean_inc(x_1);
x_201 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_180, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
lean_dec(x_201);
x_205 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
lean_inc(x_2);
x_206 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_180, x_2, x_178, x_1, x_17, x_205, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_204);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_18 = x_207;
x_19 = x_208;
goto block_26;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_206, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_206, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_180);
lean_dec(x_17);
x_213 = lean_ctor_get(x_201, 1);
lean_inc(x_213);
lean_dec(x_201);
lean_inc(x_2);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_2);
lean_ctor_set(x_214, 1, x_178);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_18 = x_215;
x_19 = x_213;
goto block_26;
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_216 = lean_ctor_get(x_201, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_201, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_218 = x_201;
} else {
 lean_dec_ref(x_201);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_189, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_189, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_222 = x_189;
} else {
 lean_dec_ref(x_189);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
else
{
lean_object* x_224; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_224 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_17, x_180, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_181);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_178);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_18 = x_230;
x_19 = x_227;
goto block_26;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_224, 1);
lean_inc(x_231);
lean_dec(x_224);
lean_inc(x_2);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_2);
lean_ctor_set(x_232, 1, x_178);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
x_18 = x_233;
x_19 = x_231;
goto block_26;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_178);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_224, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_224, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_236 = x_224;
} else {
 lean_dec_ref(x_224);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_178);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_179, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_179, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_240 = x_179;
} else {
 lean_dec_ref(x_179);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_synthesizeArgs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_toSubarray___rarg(x_3, x_13, x_12);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_get_size(x_2);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(x_1, x_15, x_2, x_18, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Meta_Simp_synthesizeArgs___closed__1;
x_25 = lean_box(0);
x_26 = lean_apply_9(x_24, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_synthesizeArgs___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_synthesizeArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":perm", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Nat_repr(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Nat_repr(x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_1, 4);
lean_inc(x_44);
x_45 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_Nat_repr(x_48);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_45, 0, x_58);
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
lean_dec(x_1);
x_62 = l_Nat_repr(x_61);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_59);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_60);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_45);
if (x_73 == 0)
{
return x_45;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_45, 0);
x_75 = lean_ctor_get(x_45, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_45);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_13);
x_14 = l_Lean_MetavarContext_getDecl(x_13, x_1);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_18 = lean_box(x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_21);
x_22 = l_Lean_MetavarContext_getDecl(x_21, x_1);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3;
x_2 = l_instInhabitedBool;
x_3 = lean_box(x_2);
x_4 = l_instInhabited___rarg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4;
x_11 = lean_panic_fn(x_10, x_1);
x_12 = lean_apply_8(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.MetavarContext", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.isLevelMVarAssignable", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unknown universe metavariable", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1;
x_2 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2;
x_3 = lean_unsigned_to_nat(412u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_6, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_free_object(x_10);
x_17 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
x_18 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_nat_dec_le(x_20, x_19);
lean_dec(x_19);
lean_dec(x_20);
x_22 = lean_box(x_21);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(x_26, x_1);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
x_29 = l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_nat_dec_le(x_31, x_30);
lean_dec(x_30);
lean_dec(x_31);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_24);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Level_hasMVar(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
x_1 = x_10;
goto _start;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Level_hasMVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_15);
x_18 = l_Lean_Level_hasMVar(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
x_1 = x_16;
goto _start;
}
}
else
{
lean_object* x_22; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_23);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_22, 0);
lean_dec(x_27);
x_28 = l_Lean_Level_hasMVar(x_16);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(x_28);
lean_ctor_set(x_22, 0, x_29);
return x_22;
}
else
{
lean_free_object(x_22);
x_1 = x_16;
x_9 = x_26;
goto _start;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_Level_hasMVar(x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
x_1 = x_16;
x_9 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_22);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_22, 0);
lean_dec(x_37);
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_22, 1);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
case 3:
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Level_hasMVar(x_44);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_44);
x_47 = l_Lean_Level_hasMVar(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
else
{
x_1 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_51 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_44, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_52);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_51, 1);
x_56 = lean_ctor_get(x_51, 0);
lean_dec(x_56);
x_57 = l_Lean_Level_hasMVar(x_45);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_58 = lean_box(x_57);
lean_ctor_set(x_51, 0, x_58);
return x_51;
}
else
{
lean_free_object(x_51);
x_1 = x_45;
x_9 = x_55;
goto _start;
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
x_61 = l_Lean_Level_hasMVar(x_45);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
x_1 = x_45;
x_9 = x_60;
goto _start;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_51, 0);
lean_dec(x_66);
return x_51;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_52);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_51);
if (x_69 == 0)
{
return x_51;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_51, 0);
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_51);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
case 5:
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
lean_dec(x_1);
x_74 = l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_74;
}
default: 
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_9);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_1 = x_14;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
case 4:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
case 5:
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_16);
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
x_1 = x_17;
goto _start;
}
}
else
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = l_Lean_Expr_hasMVar(x_17);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_box(x_29);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_free_object(x_23);
x_1 = x_17;
x_9 = x_27;
goto _start;
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Expr_hasMVar(x_17);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
x_1 = x_17;
x_9 = x_32;
goto _start;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_23, 0);
lean_dec(x_38);
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_dec(x_23);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lean_Expr_hasMVar(x_45);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_45);
x_48 = l_Lean_Expr_hasMVar(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_9);
return x_50;
}
else
{
x_1 = x_46;
goto _start;
}
}
else
{
lean_object* x_52; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_52 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_53);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_52, 1);
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = l_Lean_Expr_hasMVar(x_46);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_box(x_58);
lean_ctor_set(x_52, 0, x_59);
return x_52;
}
else
{
lean_free_object(x_52);
x_1 = x_46;
x_9 = x_56;
goto _start;
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_62 = l_Lean_Expr_hasMVar(x_46);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_box(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
else
{
x_1 = x_46;
x_9 = x_61;
goto _start;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_52);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_52, 0);
lean_dec(x_67);
return x_52;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_dec(x_52);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_52);
if (x_70 == 0)
{
return x_52;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_52, 0);
x_72 = lean_ctor_get(x_52, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_52);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
case 7:
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 2);
lean_inc(x_75);
lean_dec(x_1);
x_76 = l_Lean_Expr_hasMVar(x_74);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_74);
x_77 = l_Lean_Expr_hasMVar(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_9);
return x_79;
}
else
{
x_1 = x_75;
goto _start;
}
}
else
{
lean_object* x_81; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_82);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_81, 1);
x_86 = lean_ctor_get(x_81, 0);
lean_dec(x_86);
x_87 = l_Lean_Expr_hasMVar(x_75);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_box(x_87);
lean_ctor_set(x_81, 0, x_88);
return x_81;
}
else
{
lean_free_object(x_81);
x_1 = x_75;
x_9 = x_85;
goto _start;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_Expr_hasMVar(x_75);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
x_1 = x_75;
x_9 = x_90;
goto _start;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_81);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_81, 0);
lean_dec(x_96);
return x_81;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_81, 1);
lean_inc(x_97);
lean_dec(x_81);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_82);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_75);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_81);
if (x_99 == 0)
{
return x_81;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_81, 0);
x_101 = lean_ctor_get(x_81, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_81);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
case 8:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_1, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_1, 3);
lean_inc(x_105);
lean_dec(x_1);
x_106 = l_Lean_Expr_hasMVar(x_103);
if (x_106 == 0)
{
uint8_t x_107; 
lean_dec(x_103);
x_107 = l_Lean_Expr_hasMVar(x_104);
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_104);
x_108 = l_Lean_Expr_hasMVar(x_105);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_box(x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_9);
return x_110;
}
else
{
x_1 = x_105;
goto _start;
}
}
else
{
lean_object* x_112; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_112 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
if (x_114 == 0)
{
uint8_t x_115; 
lean_dec(x_113);
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_112, 1);
x_117 = lean_ctor_get(x_112, 0);
lean_dec(x_117);
x_118 = l_Lean_Expr_hasMVar(x_105);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_119 = lean_box(x_118);
lean_ctor_set(x_112, 0, x_119);
return x_112;
}
else
{
lean_free_object(x_112);
x_1 = x_105;
x_9 = x_116;
goto _start;
}
}
else
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_112, 1);
lean_inc(x_121);
lean_dec(x_112);
x_122 = l_Lean_Expr_hasMVar(x_105);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
else
{
x_1 = x_105;
x_9 = x_121;
goto _start;
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_126 = !lean_is_exclusive(x_112);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_112, 0);
lean_dec(x_127);
return x_112;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_112, 1);
lean_inc(x_128);
lean_dec(x_112);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_113);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_112);
if (x_130 == 0)
{
return x_112;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_112, 0);
x_132 = lean_ctor_get(x_112, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_112);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
lean_object* x_134; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_134 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_103, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
if (x_136 == 0)
{
uint8_t x_137; 
lean_dec(x_135);
x_137 = !lean_is_exclusive(x_134);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_138 = lean_ctor_get(x_134, 1);
x_139 = lean_ctor_get(x_134, 0);
lean_dec(x_139);
x_140 = l_Lean_Expr_hasMVar(x_104);
if (x_140 == 0)
{
uint8_t x_141; 
lean_dec(x_104);
x_141 = l_Lean_Expr_hasMVar(x_105);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_box(x_141);
lean_ctor_set(x_134, 0, x_142);
return x_134;
}
else
{
lean_free_object(x_134);
x_1 = x_105;
x_9 = x_138;
goto _start;
}
}
else
{
lean_object* x_144; 
lean_free_object(x_134);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_144 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_145);
x_147 = !lean_is_exclusive(x_144);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_144, 1);
x_149 = lean_ctor_get(x_144, 0);
lean_dec(x_149);
x_150 = l_Lean_Expr_hasMVar(x_105);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_151 = lean_box(x_150);
lean_ctor_set(x_144, 0, x_151);
return x_144;
}
else
{
lean_free_object(x_144);
x_1 = x_105;
x_9 = x_148;
goto _start;
}
}
else
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_144, 1);
lean_inc(x_153);
lean_dec(x_144);
x_154 = l_Lean_Expr_hasMVar(x_105);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
x_1 = x_105;
x_9 = x_153;
goto _start;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_144);
if (x_158 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_144, 0);
lean_dec(x_159);
return x_144;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_144, 1);
lean_inc(x_160);
lean_dec(x_144);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_145);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_144);
if (x_162 == 0)
{
return x_144;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_144, 0);
x_164 = lean_ctor_get(x_144, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_144);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
}
else
{
lean_object* x_166; uint8_t x_167; 
x_166 = lean_ctor_get(x_134, 1);
lean_inc(x_166);
lean_dec(x_134);
x_167 = l_Lean_Expr_hasMVar(x_104);
if (x_167 == 0)
{
uint8_t x_168; 
lean_dec(x_104);
x_168 = l_Lean_Expr_hasMVar(x_105);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_169 = lean_box(x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
else
{
x_1 = x_105;
x_9 = x_166;
goto _start;
}
}
else
{
lean_object* x_172; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_172 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_166);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec(x_173);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_176 = x_172;
} else {
 lean_dec_ref(x_172);
 x_176 = lean_box(0);
}
x_177 = l_Lean_Expr_hasMVar(x_105);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_box(x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
return x_179;
}
else
{
lean_dec(x_176);
x_1 = x_105;
x_9 = x_175;
goto _start;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_ctor_get(x_172, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_182 = x_172;
} else {
 lean_dec_ref(x_172);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_173);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_ctor_get(x_172, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_172, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_186 = x_172;
} else {
 lean_dec_ref(x_172);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_134);
if (x_188 == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_134, 0);
lean_dec(x_189);
return x_134;
}
else
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_134, 1);
lean_inc(x_190);
lean_dec(x_134);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_135);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_134);
if (x_192 == 0)
{
return x_134;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_134, 0);
x_194 = lean_ctor_get(x_134, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_134);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
}
case 10:
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_1, 1);
lean_inc(x_196);
lean_dec(x_1);
x_197 = l_Lean_Expr_hasMVar(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_196);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_198 = lean_box(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_9);
return x_199;
}
else
{
x_1 = x_196;
goto _start;
}
}
case 11:
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_1, 2);
lean_inc(x_201);
lean_dec(x_1);
x_202 = l_Lean_Expr_hasMVar(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_203 = lean_box(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_9);
return x_204;
}
else
{
x_1 = x_201;
goto _start;
}
}
default: 
{
uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = 0;
x_207 = lean_box(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_9);
return x_208;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Meta_Simp_recordSimpTheorem(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = 1;
x_18 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_3);
lean_ctor_set_uint32(x_18, sizeof(void*)*2, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 4, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = 0;
x_22 = 1;
x_23 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
lean_ctor_set_uint32(x_23, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 4, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ==> ", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_6);
x_15 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(x_1, x_2, x_3, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_MessageData_ofExpr(x_5);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_2);
x_34 = l_Lean_MessageData_ofExpr(x_2);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
x_37 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_15, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(x_1, x_2, x_3, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_38);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_23);
if (x_41 == 0)
{
return x_23;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_23, 0);
x_43 = lean_ctor_get(x_23, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", perm rejected ", 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
lean_dec(x_6);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_2);
x_19 = l_Lean_Meta_ACLt_main_lt(x_18, x_2, x_5, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_28 = lean_unbox(x_25);
lean_dec(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_apply_9(x_27, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofExpr(x_5);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofExpr(x_2);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
x_45 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_23, x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_9(x_27, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_31, 0);
x_51 = lean_ctor_get(x_31, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_31);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_box(0);
x_55 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_54, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_53);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_19 = lean_expr_eqv(x_4, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(x_2, x_18, x_5, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_26 = lean_expr_eqv(x_4, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(x_2, x_25, x_5, x_3, x_4, x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_apply_9(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", has unassigned metavariables after unification", 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
lean_dec(x_7);
x_16 = lean_ctor_get_uint8(x_3, sizeof(void*)*5 + 2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_3);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5), 13, 4);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_4);
x_18 = l_Lean_mkAppN(x_5, x_6);
x_19 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_20);
x_22 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(x_20, x_17, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_20);
lean_dec(x_17);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_30 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_29, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_34 = lean_unbox(x_31);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
x_35 = lean_box(0);
x_36 = lean_apply_9(x_33, x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_29, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_apply_9(x_33, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_48 = !lean_is_exclusive(x_37);
if (x_48 == 0)
{
return x_37;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_37, 0);
x_50 = lean_ctor_get(x_37, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_37);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_22);
if (x_52 == 0)
{
return x_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_22, 0);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_22);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_5);
x_56 = lean_box(0);
x_57 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(x_1, x_2, x_3, x_4, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_57;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unify", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", failed to unify", 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nwith", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
lean_inc(x_1);
x_16 = l_Lean_Meta_isExprDefEq(x_1, x_7, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_21 = l_Lean_Expr_isMVar(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2;
x_23 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_apply_9(x_20, x_27, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_indentExpr(x_1);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentExpr(x_7);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
x_44 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_22, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_apply_9(x_20, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_apply_9(x_20, x_52, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_19);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_dec(x_16);
x_55 = lean_ctor_get(x_6, 4);
lean_inc(x_55);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_55);
x_56 = l_Lean_Meta_Simp_synthesizeArgs(x_55, x_2, x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_56, 0, x_61);
return x_56;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_dec(x_56);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_56, 1);
lean_inc(x_65);
lean_dec(x_56);
x_66 = lean_box(0);
x_67 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(x_5, x_55, x_6, x_7, x_4, x_2, x_66, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
return x_56;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_56, 0);
x_70 = lean_ctor_get(x_56, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_56);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_16);
if (x_72 == 0)
{
return x_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_16, 0);
x_74 = lean_ctor_get(x_16, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_16);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Result_addExtraArgs(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", resulting expression has unassigned metavariables", 51);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_21 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try___spec__1(x_8, x_19, x_8, x_20, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Array_reverse___rarg(x_25);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_38 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_37, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_7);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(x_36, x_26, x_42, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_36);
lean_dec(x_26);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_46 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_45, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
x_61 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_45, x_62, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_58);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_dec(x_65);
x_66 = lean_box(0);
lean_ctor_set(x_63, 0, x_66);
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_70 = !lean_is_exclusive(x_56);
if (x_70 == 0)
{
return x_56;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_56, 0);
x_72 = lean_ctor_get(x_56, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_56);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_74 = !lean_is_exclusive(x_38);
if (x_74 == 0)
{
return x_38;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_38, 0);
x_76 = lean_ctor_get(x_38, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_38);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_78 = !lean_is_exclusive(x_27);
if (x_78 == 0)
{
return x_27;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_27, 0);
x_80 = lean_ctor_get(x_27, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_27);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = lean_apply_8(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 10, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_apply_3(x_1, x_3, x_4, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(x_2, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_13 = lean_infer_type(x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 1;
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_14, x_17, x_16, x_18, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = lean_whnf(x_27, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_30);
x_32 = l_Lean_Expr_appFn_x21(x_30);
x_33 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_34 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_33, x_23, x_24, x_4, x_30, x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2), 12, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 10, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = 0;
x_16 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_12 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = 1;
x_17 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_13, x_16, x_15, x_17, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_28 = lean_whnf(x_26, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_29);
x_31 = l_Lean_Expr_appFn_x21(x_29);
x_32 = l_Lean_Expr_appArg_x21(x_31);
lean_dec(x_31);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_29);
lean_inc(x_3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_32);
x_34 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_32, x_22, x_23, x_3, x_29, x_1, x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_33);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_33);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_34, 0, x_15);
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_34);
x_42 = lean_nat_sub(x_40, x_39);
lean_dec(x_39);
lean_dec(x_40);
x_43 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_32, x_22, x_23, x_3, x_29, x_1, x_2, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_37);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_32, x_33);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_33);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_15);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_nat_sub(x_46, x_45);
lean_dec(x_45);
lean_dec(x_46);
x_50 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_32, x_22, x_23, x_3, x_29, x_1, x_2, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_34);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_34, 0);
lean_dec(x_52);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
lean_dec(x_35);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_34, 0, x_55);
return x_34;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_dec(x_34);
x_57 = lean_ctor_get(x_35, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_58 = x_35;
} else {
 lean_dec_ref(x_35);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_56);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_34);
if (x_61 == 0)
{
return x_34;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_34, 0);
x_63 = lean_ctor_get(x_34, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_34);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_28);
if (x_65 == 0)
{
return x_28;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_28, 0);
x_67 = lean_ctor_get(x_28, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_28);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_18);
if (x_69 == 0)
{
return x_18;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_18, 0);
x_71 = lean_ctor_get(x_18, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_18);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1), 11, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 10, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = 0;
x_15 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_isLemma___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_array_fget(x_1, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_nat_dec_lt(x_11, x_13);
lean_dec(x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fswap(x_1, x_2, x_7);
lean_dec(x_2);
x_1 = x_15;
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(x_1, x_2, lean_box(0));
x_11 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_7;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Debug", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_4 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rewrite result ", 15);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" => ", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_7, x_6);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_69; 
lean_dec(x_8);
x_19 = lean_array_uget(x_5, x_7);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
lean_inc(x_29);
lean_inc(x_2);
x_69 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_2, x_29);
if (x_69 == 0)
{
if (x_3 == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_31 = x_70;
goto block_68;
}
else
{
uint8_t x_71; 
x_71 = lean_ctor_get_uint8(x_29, sizeof(void*)*5 + 2);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_4);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_4);
x_20 = x_72;
x_21 = x_16;
goto block_28;
}
else
{
lean_object* x_73; 
x_73 = lean_box(0);
x_31 = x_73;
goto block_68;
}
}
}
else
{
lean_object* x_74; 
lean_dec(x_30);
lean_dec(x_29);
lean_inc(x_4);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_4);
x_20 = x_74;
x_21 = x_16;
goto block_28;
}
block_28:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_7 = x_26;
x_8 = x_24;
x_16 = x_21;
goto _start;
}
}
block_68:
{
lean_object* x_32; 
lean_dec(x_31);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_32 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(x_1, x_29, x_30, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_4);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_4);
x_20 = x_35;
x_21 = x_34;
goto block_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
x_39 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_38, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_37, x_43, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_20 = x_45;
x_21 = x_46;
goto block_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
lean_inc(x_1);
x_48 = l_Lean_MessageData_ofExpr(x_1);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_ctor_get(x_37, 0);
lean_inc(x_53);
x_54 = l_Lean_MessageData_ofExpr(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_38, x_57, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_47);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_37, x_59, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_60);
lean_dec(x_59);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_20 = x_62;
x_21 = x_63;
goto block_28;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_32);
if (x_64 == 0)
{
return x_32;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_32, 0);
x_66 = lean_ctor_get(x_32, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_32);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("no theorems found for ", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite_x3f___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("-rewriting ", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewrite_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_rewrite_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_Meta_Simp_getConfig___rarg(x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Simp_getDtConfig(x_15);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_18 = l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(x_2, x_1, x_17, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_isEmpty___rarg(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_array_get_size(x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(x_19, x_23, x_22);
x_25 = lean_box(0);
x_26 = lean_array_get_size(x_24);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = 0;
x_29 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
x_30 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(x_1, x_3, x_5, x_29, x_24, x_27, x_28, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_25);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_3);
x_47 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
x_48 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_52 = lean_unbox(x_49);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_apply_9(x_51, x_53, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = l_Lean_stringToMessageData(x_4);
x_56 = l_Lean_Meta_Simp_rewrite_x3f___closed__3;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Meta_Simp_rewrite_x3f___closed__5;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_MessageData_ofExpr(x_1);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_47, x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_apply_9(x_51, x_65, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
return x_18;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(x_1, x_2, x_17, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_rewrite_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_nat_sub(x_10, x_9);
lean_dec(x_10);
x_12 = l_Lean_Expr_getRevArg_x21(x_2, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_8);
x_10 = lean_nat_sub(x_9, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Expr_getRevArg_x21(x_1, x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = l_Lean_Meta_whnfD(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2;
x_19 = l_Lean_Expr_isConstOf(x_16, x_18);
lean_dec(x_16);
if (x_19 == 0)
{
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
x_20 = lean_box(0);
x_21 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1(x_9, x_1, x_20, x_3, x_4, x_5, x_6, x_17);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_dec(x_9);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2;
x_25 = l_Lean_Expr_isConstOf(x_22, x_24);
lean_dec(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_box(0);
x_28 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1(x_9, x_1, x_27, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_dec(x_9);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("OfNat", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ofNat", 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__3;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2(x_1, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg___lambda__1), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg___boxed), 13, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__3;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_11 = l_Lean_Meta_mkNoConfusion(x_10, x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_15 = lean_array_push(x_14, x_1);
x_16 = 0;
x_17 = 1;
x_18 = 1;
x_19 = l_Lean_Meta_mkLambdaFVars(x_15, x_12, x_16, x_17, x_18, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
lean_ctor_set_uint8(x_20, 9, x_26);
x_27 = l_Lean_Meta_mkEqFalse_x27(x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = 0;
x_32 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set_uint32(x_32, sizeof(void*)*2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 4, x_17);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint32_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = 0;
x_38 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set_uint32(x_38, sizeof(void*)*2, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*2 + 4, x_17);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get_uint8(x_20, 0);
x_46 = lean_ctor_get_uint8(x_20, 1);
x_47 = lean_ctor_get_uint8(x_20, 2);
x_48 = lean_ctor_get_uint8(x_20, 3);
x_49 = lean_ctor_get_uint8(x_20, 4);
x_50 = lean_ctor_get_uint8(x_20, 5);
x_51 = lean_ctor_get_uint8(x_20, 6);
x_52 = lean_ctor_get_uint8(x_20, 7);
x_53 = lean_ctor_get_uint8(x_20, 8);
x_54 = lean_ctor_get_uint8(x_20, 10);
x_55 = lean_ctor_get_uint8(x_20, 11);
lean_dec(x_20);
x_56 = 1;
x_57 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_57, 0, x_45);
lean_ctor_set_uint8(x_57, 1, x_46);
lean_ctor_set_uint8(x_57, 2, x_47);
lean_ctor_set_uint8(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, 4, x_49);
lean_ctor_set_uint8(x_57, 5, x_50);
lean_ctor_set_uint8(x_57, 6, x_51);
lean_ctor_set_uint8(x_57, 7, x_52);
lean_ctor_set_uint8(x_57, 8, x_53);
lean_ctor_set_uint8(x_57, 9, x_56);
lean_ctor_set_uint8(x_57, 10, x_54);
lean_ctor_set_uint8(x_57, 11, x_55);
lean_ctor_set(x_5, 0, x_57);
x_58 = l_Lean_Meta_mkEqFalse_x27(x_21, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_59);
x_63 = 0;
x_64 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_64, 0, x_10);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set_uint32(x_64, sizeof(void*)*2, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2 + 4, x_17);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_58, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_58, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_71 = lean_ctor_get(x_5, 1);
x_72 = lean_ctor_get(x_5, 2);
x_73 = lean_ctor_get(x_5, 3);
x_74 = lean_ctor_get(x_5, 4);
x_75 = lean_ctor_get(x_5, 5);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_5);
x_76 = lean_ctor_get_uint8(x_20, 0);
x_77 = lean_ctor_get_uint8(x_20, 1);
x_78 = lean_ctor_get_uint8(x_20, 2);
x_79 = lean_ctor_get_uint8(x_20, 3);
x_80 = lean_ctor_get_uint8(x_20, 4);
x_81 = lean_ctor_get_uint8(x_20, 5);
x_82 = lean_ctor_get_uint8(x_20, 6);
x_83 = lean_ctor_get_uint8(x_20, 7);
x_84 = lean_ctor_get_uint8(x_20, 8);
x_85 = lean_ctor_get_uint8(x_20, 10);
x_86 = lean_ctor_get_uint8(x_20, 11);
if (lean_is_exclusive(x_20)) {
 x_87 = x_20;
} else {
 lean_dec_ref(x_20);
 x_87 = lean_box(0);
}
x_88 = 1;
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 0, 12);
} else {
 x_89 = x_87;
}
lean_ctor_set_uint8(x_89, 0, x_76);
lean_ctor_set_uint8(x_89, 1, x_77);
lean_ctor_set_uint8(x_89, 2, x_78);
lean_ctor_set_uint8(x_89, 3, x_79);
lean_ctor_set_uint8(x_89, 4, x_80);
lean_ctor_set_uint8(x_89, 5, x_81);
lean_ctor_set_uint8(x_89, 6, x_82);
lean_ctor_set_uint8(x_89, 7, x_83);
lean_ctor_set_uint8(x_89, 8, x_84);
lean_ctor_set_uint8(x_89, 9, x_88);
lean_ctor_set_uint8(x_89, 10, x_85);
lean_ctor_set_uint8(x_89, 11, x_86);
x_90 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_71);
lean_ctor_set(x_90, 2, x_72);
lean_ctor_set(x_90, 3, x_73);
lean_ctor_set(x_90, 4, x_74);
lean_ctor_set(x_90, 5, x_75);
x_91 = l_Lean_Meta_mkEqFalse_x27(x_21, x_90, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint32_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_92);
x_96 = 0;
x_97 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_97, 0, x_10);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set_uint32(x_97, sizeof(void*)*2, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 4, x_17);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (lean_is_scalar(x_94)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_94;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_91, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_102 = x_91;
} else {
 lean_dec_ref(x_91);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_104 = !lean_is_exclusive(x_19);
if (x_104 == 0)
{
return x_19;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_19, 0);
x_106 = lean_ctor_get(x_19, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_19);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_11);
if (x_108 == 0)
{
return x_11;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_11, 0);
x_110 = lean_ctor_get(x_11, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_11);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpCtorEq___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpCtorEq___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpCtorEq___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpCtorEq___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpCtorEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Simp_simpCtorEq___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_1);
x_15 = l_Lean_Expr_appFn_x21(x_1);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_Lean_Expr_appArg_x21(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
x_21 = 3;
lean_ctor_set_uint8(x_19, 9, x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = lean_whnf(x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(x_23, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = lean_whnf(x_17, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(x_29, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_st_ref_get(x_8, x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = 0;
lean_inc(x_38);
x_40 = l_Lean_Expr_constructorApp_x3f(x_38, x_26, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_34, 0, x_41);
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_constructorApp_x3f(x_38, x_32, x_39);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_34, 0, x_44);
return x_34;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_name_eq(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_free_object(x_34);
x_53 = l_Lean_Meta_Simp_simpCtorEq___closed__5;
x_54 = 0;
x_55 = l_Lean_Meta_Simp_simpCtorEq___closed__6;
x_56 = 0;
x_57 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(x_53, x_54, x_1, x_55, x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_34, 0, x_66);
return x_34;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_34, 0);
x_68 = lean_ctor_get(x_34, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_34);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = 0;
lean_inc(x_69);
x_71 = l_Lean_Expr_constructorApp_x3f(x_69, x_26, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_69);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_Expr_constructorApp_x3f(x_69, x_32, x_70);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_74);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_68);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_80, 0);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_name_eq(x_82, x_84);
lean_dec(x_84);
lean_dec(x_82);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_86 = l_Lean_Meta_Simp_simpCtorEq___closed__5;
x_87 = 0;
x_88 = l_Lean_Meta_Simp_simpCtorEq___closed__6;
x_89 = 0;
x_90 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(x_86, x_87, x_1, x_88, x_89, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_97 = x_90;
} else {
 lean_dec_ref(x_90);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_68);
return x_100;
}
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_31);
if (x_101 == 0)
{
return x_31;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_31, 0);
x_103 = lean_ctor_get(x_31, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_31);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_28);
if (x_105 == 0)
{
return x_28;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_28, 0);
x_107 = lean_ctor_get(x_28, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_28);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_25);
if (x_109 == 0)
{
return x_25;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_25, 0);
x_111 = lean_ctor_get(x_25, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_25);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_22);
if (x_113 == 0)
{
return x_22;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_22, 0);
x_115 = lean_ctor_get(x_22, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_22);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
x_117 = lean_ctor_get_uint8(x_19, 0);
x_118 = lean_ctor_get_uint8(x_19, 1);
x_119 = lean_ctor_get_uint8(x_19, 2);
x_120 = lean_ctor_get_uint8(x_19, 3);
x_121 = lean_ctor_get_uint8(x_19, 4);
x_122 = lean_ctor_get_uint8(x_19, 5);
x_123 = lean_ctor_get_uint8(x_19, 6);
x_124 = lean_ctor_get_uint8(x_19, 7);
x_125 = lean_ctor_get_uint8(x_19, 8);
x_126 = lean_ctor_get_uint8(x_19, 10);
x_127 = lean_ctor_get_uint8(x_19, 11);
lean_dec(x_19);
x_128 = 3;
x_129 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_129, 0, x_117);
lean_ctor_set_uint8(x_129, 1, x_118);
lean_ctor_set_uint8(x_129, 2, x_119);
lean_ctor_set_uint8(x_129, 3, x_120);
lean_ctor_set_uint8(x_129, 4, x_121);
lean_ctor_set_uint8(x_129, 5, x_122);
lean_ctor_set_uint8(x_129, 6, x_123);
lean_ctor_set_uint8(x_129, 7, x_124);
lean_ctor_set_uint8(x_129, 8, x_125);
lean_ctor_set_uint8(x_129, 9, x_128);
lean_ctor_set_uint8(x_129, 10, x_126);
lean_ctor_set_uint8(x_129, 11, x_127);
lean_ctor_set(x_5, 0, x_129);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_130 = lean_whnf(x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_133 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(x_131, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = lean_whnf(x_17, x_5, x_6, x_7, x_8, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_139 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(x_137, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_st_ref_get(x_8, x_141);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
lean_dec(x_143);
x_147 = 0;
lean_inc(x_146);
x_148 = l_Lean_Expr_constructorApp_x3f(x_146, x_134, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_146);
lean_dec(x_140);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_144);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
lean_dec(x_148);
x_152 = l_Lean_Expr_constructorApp_x3f(x_146, x_140, x_147);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_145)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_145;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
lean_dec(x_152);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
lean_dec(x_151);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_name_eq(x_159, x_161);
lean_dec(x_161);
lean_dec(x_159);
if (x_162 == 0)
{
lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
lean_dec(x_145);
x_163 = l_Lean_Meta_Simp_simpCtorEq___closed__5;
x_164 = 0;
x_165 = l_Lean_Meta_Simp_simpCtorEq___closed__6;
x_166 = 0;
x_167 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(x_163, x_164, x_1, x_165, x_166, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_144);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_167, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_174 = x_167;
} else {
 lean_dec_ref(x_167);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_176 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_145)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_145;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_144);
return x_177;
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_134);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_ctor_get(x_139, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_139, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_180 = x_139;
} else {
 lean_dec_ref(x_139);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_134);
lean_dec(x_5);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_136, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_136, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_184 = x_136;
} else {
 lean_dec_ref(x_136);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_133, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_133, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_188 = x_133;
} else {
 lean_dec_ref(x_133);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_5);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_130, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_130, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_192 = x_130;
} else {
 lean_dec_ref(x_130);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_190);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_194 = lean_ctor_get(x_5, 0);
x_195 = lean_ctor_get(x_5, 1);
x_196 = lean_ctor_get(x_5, 2);
x_197 = lean_ctor_get(x_5, 3);
x_198 = lean_ctor_get(x_5, 4);
x_199 = lean_ctor_get(x_5, 5);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_5);
x_200 = lean_ctor_get_uint8(x_194, 0);
x_201 = lean_ctor_get_uint8(x_194, 1);
x_202 = lean_ctor_get_uint8(x_194, 2);
x_203 = lean_ctor_get_uint8(x_194, 3);
x_204 = lean_ctor_get_uint8(x_194, 4);
x_205 = lean_ctor_get_uint8(x_194, 5);
x_206 = lean_ctor_get_uint8(x_194, 6);
x_207 = lean_ctor_get_uint8(x_194, 7);
x_208 = lean_ctor_get_uint8(x_194, 8);
x_209 = lean_ctor_get_uint8(x_194, 10);
x_210 = lean_ctor_get_uint8(x_194, 11);
if (lean_is_exclusive(x_194)) {
 x_211 = x_194;
} else {
 lean_dec_ref(x_194);
 x_211 = lean_box(0);
}
x_212 = 3;
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(0, 0, 12);
} else {
 x_213 = x_211;
}
lean_ctor_set_uint8(x_213, 0, x_200);
lean_ctor_set_uint8(x_213, 1, x_201);
lean_ctor_set_uint8(x_213, 2, x_202);
lean_ctor_set_uint8(x_213, 3, x_203);
lean_ctor_set_uint8(x_213, 4, x_204);
lean_ctor_set_uint8(x_213, 5, x_205);
lean_ctor_set_uint8(x_213, 6, x_206);
lean_ctor_set_uint8(x_213, 7, x_207);
lean_ctor_set_uint8(x_213, 8, x_208);
lean_ctor_set_uint8(x_213, 9, x_212);
lean_ctor_set_uint8(x_213, 10, x_209);
lean_ctor_set_uint8(x_213, 11, x_210);
x_214 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_195);
lean_ctor_set(x_214, 2, x_196);
lean_ctor_set(x_214, 3, x_197);
lean_ctor_set(x_214, 4, x_198);
lean_ctor_set(x_214, 5, x_199);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_214);
x_215 = lean_whnf(x_16, x_214, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_214);
x_218 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(x_216, x_214, x_6, x_7, x_8, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_214);
x_221 = lean_whnf(x_17, x_214, x_6, x_7, x_8, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_214);
x_224 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat(x_222, x_214, x_6, x_7, x_8, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = lean_st_ref_get(x_8, x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_230 = x_227;
} else {
 lean_dec_ref(x_227);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = 0;
lean_inc(x_231);
x_233 = l_Lean_Expr_constructorApp_x3f(x_231, x_219, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
lean_dec(x_225);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_230)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_230;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_229);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
lean_dec(x_233);
x_237 = l_Lean_Expr_constructorApp_x3f(x_231, x_225, x_232);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_236);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_230)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_230;
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_229);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_240 = lean_ctor_get(x_237, 0);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_236, 0);
lean_inc(x_241);
lean_dec(x_236);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
lean_dec(x_243);
x_245 = lean_ctor_get(x_242, 0);
lean_inc(x_245);
lean_dec(x_242);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec(x_245);
x_247 = lean_name_eq(x_244, x_246);
lean_dec(x_246);
lean_dec(x_244);
if (x_247 == 0)
{
lean_object* x_248; uint8_t x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
lean_dec(x_230);
x_248 = l_Lean_Meta_Simp_simpCtorEq___closed__5;
x_249 = 0;
x_250 = l_Lean_Meta_Simp_simpCtorEq___closed__6;
x_251 = 0;
x_252 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(x_248, x_249, x_1, x_250, x_251, x_2, x_3, x_4, x_214, x_6, x_7, x_8, x_229);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_252, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_252, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_259 = x_252;
} else {
 lean_dec_ref(x_252);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_230)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_230;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_229);
return x_262;
}
}
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_219);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_ctor_get(x_224, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_224, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_265 = x_224;
} else {
 lean_dec_ref(x_224);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_219);
lean_dec(x_214);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_ctor_get(x_221, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_221, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_269 = x_221;
} else {
 lean_dec_ref(x_221);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_214);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_271 = lean_ctor_get(x_218, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_218, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_273 = x_218;
} else {
 lean_dec_ref(x_218);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_214);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = lean_ctor_get(x_215, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_215, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_277 = x_215;
} else {
 lean_dec_ref(x_215);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_simpCtorEq___spec__1___rarg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpCtorEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_simpCtorEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1;
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1;
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false_of_decide", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__14;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true_of_decide", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__17;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_21; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_21 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_6, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_6, 5);
lean_inc(x_29);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_31 = 1;
lean_ctor_set_uint8(x_22, 9, x_31);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_28);
lean_ctor_set(x_32, 5, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
x_33 = lean_whnf(x_23, x_32, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3;
x_38 = l_Lean_Expr_isConstOf(x_35, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5;
x_40 = l_Lean_Expr_isConstOf(x_35, x_39);
lean_dec(x_35);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_41 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_33, 0, x_41);
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_free_object(x_33);
x_42 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6;
lean_inc(x_8);
x_43 = l_Lean_Meta_mkEqRefl(x_42, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_8);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint32_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_47 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_48 = lean_array_push(x_47, x_1);
x_49 = lean_array_push(x_48, x_46);
x_50 = lean_array_push(x_49, x_45);
x_51 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10;
x_52 = l_Lean_mkAppN(x_51, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = 0;
x_55 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7;
x_56 = 1;
x_57 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set_uint32(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 4, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_43, 0, x_58);
return x_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint32_t x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_59 = lean_ctor_get(x_43, 0);
x_60 = lean_ctor_get(x_43, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_43);
x_61 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_62 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_63 = lean_array_push(x_62, x_1);
x_64 = lean_array_push(x_63, x_61);
x_65 = lean_array_push(x_64, x_59);
x_66 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10;
x_67 = l_Lean_mkAppN(x_66, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = 0;
x_70 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7;
x_71 = 1;
x_72 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_68);
lean_ctor_set_uint32(x_72, sizeof(void*)*2, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*2 + 4, x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_60);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_23);
lean_dec(x_1);
x_75 = lean_ctor_get(x_43, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_43, 1);
lean_inc(x_76);
lean_dec(x_43);
x_11 = x_75;
x_12 = x_76;
goto block_20;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_free_object(x_33);
lean_dec(x_35);
x_77 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12;
lean_inc(x_8);
x_78 = l_Lean_Meta_mkEqRefl(x_77, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
lean_dec(x_8);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint32_t x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_82 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_83 = lean_array_push(x_82, x_1);
x_84 = lean_array_push(x_83, x_81);
x_85 = lean_array_push(x_84, x_80);
x_86 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18;
x_87 = l_Lean_mkAppN(x_86, x_85);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = 0;
x_90 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15;
x_91 = 1;
x_92 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_88);
lean_ctor_set_uint32(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 4, x_91);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_78, 0, x_93);
return x_78;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint32_t x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_94 = lean_ctor_get(x_78, 0);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_78);
x_96 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_97 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_94);
x_101 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18;
x_102 = l_Lean_mkAppN(x_101, x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = 0;
x_105 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15;
x_106 = 1;
x_107 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_103);
lean_ctor_set_uint32(x_107, sizeof(void*)*2, x_104);
lean_ctor_set_uint8(x_107, sizeof(void*)*2 + 4, x_106);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_95);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_23);
lean_dec(x_1);
x_110 = lean_ctor_get(x_78, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_78, 1);
lean_inc(x_111);
lean_dec(x_78);
x_11 = x_110;
x_12 = x_111;
goto block_20;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_33, 0);
x_113 = lean_ctor_get(x_33, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_33);
x_114 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3;
x_115 = l_Lean_Expr_isConstOf(x_112, x_114);
if (x_115 == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5;
x_117 = l_Lean_Expr_isConstOf(x_112, x_116);
lean_dec(x_112);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_118 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6;
lean_inc(x_8);
x_121 = l_Lean_Meta_mkEqRefl(x_120, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint32_t x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_8);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_126 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_127 = lean_array_push(x_126, x_1);
x_128 = lean_array_push(x_127, x_125);
x_129 = lean_array_push(x_128, x_122);
x_130 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10;
x_131 = l_Lean_mkAppN(x_130, x_129);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = 0;
x_134 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7;
x_135 = 1;
x_136 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_132);
lean_ctor_set_uint32(x_136, sizeof(void*)*2, x_133);
lean_ctor_set_uint8(x_136, sizeof(void*)*2 + 4, x_135);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
if (lean_is_scalar(x_124)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_124;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_123);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_23);
lean_dec(x_1);
x_139 = lean_ctor_get(x_121, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_121, 1);
lean_inc(x_140);
lean_dec(x_121);
x_11 = x_139;
x_12 = x_140;
goto block_20;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_112);
x_141 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12;
lean_inc(x_8);
x_142 = l_Lean_Meta_mkEqRefl(x_141, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint32_t x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_8);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_147 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_148 = lean_array_push(x_147, x_1);
x_149 = lean_array_push(x_148, x_146);
x_150 = lean_array_push(x_149, x_143);
x_151 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18;
x_152 = l_Lean_mkAppN(x_151, x_150);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
x_154 = 0;
x_155 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15;
x_156 = 1;
x_157 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_153);
lean_ctor_set_uint32(x_157, sizeof(void*)*2, x_154);
lean_ctor_set_uint8(x_157, sizeof(void*)*2 + 4, x_156);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_157);
if (lean_is_scalar(x_145)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_145;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_144);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_23);
lean_dec(x_1);
x_160 = lean_ctor_get(x_142, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_142, 1);
lean_inc(x_161);
lean_dec(x_142);
x_11 = x_160;
x_12 = x_161;
goto block_20;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_162 = lean_ctor_get(x_33, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_33, 1);
lean_inc(x_163);
lean_dec(x_33);
x_11 = x_162;
x_12 = x_163;
goto block_20;
}
}
else
{
uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_164 = lean_ctor_get_uint8(x_22, 0);
x_165 = lean_ctor_get_uint8(x_22, 1);
x_166 = lean_ctor_get_uint8(x_22, 2);
x_167 = lean_ctor_get_uint8(x_22, 3);
x_168 = lean_ctor_get_uint8(x_22, 4);
x_169 = lean_ctor_get_uint8(x_22, 5);
x_170 = lean_ctor_get_uint8(x_22, 6);
x_171 = lean_ctor_get_uint8(x_22, 7);
x_172 = lean_ctor_get_uint8(x_22, 8);
x_173 = lean_ctor_get_uint8(x_22, 10);
x_174 = lean_ctor_get_uint8(x_22, 11);
lean_dec(x_22);
x_175 = 1;
x_176 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_176, 0, x_164);
lean_ctor_set_uint8(x_176, 1, x_165);
lean_ctor_set_uint8(x_176, 2, x_166);
lean_ctor_set_uint8(x_176, 3, x_167);
lean_ctor_set_uint8(x_176, 4, x_168);
lean_ctor_set_uint8(x_176, 5, x_169);
lean_ctor_set_uint8(x_176, 6, x_170);
lean_ctor_set_uint8(x_176, 7, x_171);
lean_ctor_set_uint8(x_176, 8, x_172);
lean_ctor_set_uint8(x_176, 9, x_175);
lean_ctor_set_uint8(x_176, 10, x_173);
lean_ctor_set_uint8(x_176, 11, x_174);
x_177 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_25);
lean_ctor_set(x_177, 2, x_26);
lean_ctor_set(x_177, 3, x_27);
lean_ctor_set(x_177, 4, x_28);
lean_ctor_set(x_177, 5, x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
x_178 = lean_whnf(x_23, x_177, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3;
x_183 = l_Lean_Expr_isConstOf(x_179, x_182);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5;
x_185 = l_Lean_Expr_isConstOf(x_179, x_184);
lean_dec(x_179);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_186 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
if (lean_is_scalar(x_181)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_181;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_180);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_181);
x_188 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6;
lean_inc(x_8);
x_189 = l_Lean_Meta_mkEqRefl(x_188, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint32_t x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_8);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_194 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_195 = lean_array_push(x_194, x_1);
x_196 = lean_array_push(x_195, x_193);
x_197 = lean_array_push(x_196, x_190);
x_198 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10;
x_199 = l_Lean_mkAppN(x_198, x_197);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
x_201 = 0;
x_202 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7;
x_203 = 1;
x_204 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_200);
lean_ctor_set_uint32(x_204, sizeof(void*)*2, x_201);
lean_ctor_set_uint8(x_204, sizeof(void*)*2 + 4, x_203);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
if (lean_is_scalar(x_192)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_192;
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_191);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_23);
lean_dec(x_1);
x_207 = lean_ctor_get(x_189, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_189, 1);
lean_inc(x_208);
lean_dec(x_189);
x_11 = x_207;
x_12 = x_208;
goto block_20;
}
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_181);
lean_dec(x_179);
x_209 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12;
lean_inc(x_8);
x_210 = l_Lean_Meta_mkEqRefl(x_209, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint32_t x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_8);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Expr_appArg_x21(x_23);
lean_dec(x_23);
x_215 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11;
x_216 = lean_array_push(x_215, x_1);
x_217 = lean_array_push(x_216, x_214);
x_218 = lean_array_push(x_217, x_211);
x_219 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18;
x_220 = l_Lean_mkAppN(x_219, x_218);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = 0;
x_223 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15;
x_224 = 1;
x_225 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_221);
lean_ctor_set_uint32(x_225, sizeof(void*)*2, x_222);
lean_ctor_set_uint8(x_225, sizeof(void*)*2 + 4, x_224);
x_226 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_226, 0, x_225);
if (lean_is_scalar(x_213)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_213;
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_212);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_23);
lean_dec(x_1);
x_228 = lean_ctor_get(x_210, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_210, 1);
lean_inc(x_229);
lean_dec(x_210);
x_11 = x_228;
x_12 = x_229;
goto block_20;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_230 = lean_ctor_get(x_178, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_178, 1);
lean_inc(x_231);
lean_dec(x_178);
x_11 = x_230;
x_12 = x_231;
goto block_20;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_232 = lean_ctor_get(x_21, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_21, 1);
lean_inc(x_233);
lean_dec(x_21);
x_11 = x_232;
x_12 = x_233;
goto block_20;
}
block_20:
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_8);
x_14 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
x_18 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = l_Lean_Expr_hasFVar(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasMVar(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
lean_inc(x_1);
x_13 = l_Lean_Expr_isTrue(x_1);
if (x_13 == 0)
{
uint8_t x_14; 
lean_inc(x_1);
x_14 = l_Lean_Expr_isFalse(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_21 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Simp_getConfig___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 9);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_simpUsingDecide___lambda__2(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpUsingDecide___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpUsingDecide___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpUsingDecide___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Linear_Nat_simpExpr_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_12, 0, x_24);
x_25 = 0;
x_26 = 1;
x_27 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set_uint32(x_27, sizeof(void*)*2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*2 + 4, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_11, 0, x_28);
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_ctor_set(x_12, 0, x_32);
x_33 = 0;
x_34 = 1;
x_35 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set_uint32(x_35, sizeof(void*)*2, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 4, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_12, 0);
lean_inc(x_38);
lean_dec(x_12);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_40 = x_11;
} else {
 lean_dec_ref(x_11);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = 0;
x_45 = 1;
x_46 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set_uint32(x_46, sizeof(void*)*2, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 4, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_40)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_40;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_11);
if (x_49 == 0)
{
return x_11;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_11, 0);
x_51 = lean_ctor_get(x_11, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_11);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Meta_Linear_isLinearCnstr(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Meta_Linear_isLinearTerm(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
x_16 = l_Lean_Meta_Linear_parentIsTarget(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Simp_simpArith___lambda__1(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_18;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = 0;
x_21 = 0;
x_22 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint32(x_22, sizeof(void*)*2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 4, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_4);
x_26 = l_Lean_Meta_Linear_Nat_simpCnstr_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint32_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_26, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_ctor_set(x_27, 0, x_39);
x_40 = 0;
x_41 = 1;
x_42 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_27);
lean_ctor_set_uint32(x_42, sizeof(void*)*2, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 4, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_26, 0, x_43);
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint32_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_dec(x_26);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set(x_27, 0, x_47);
x_48 = 0;
x_49 = 1;
x_50 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_27);
lean_ctor_set_uint32(x_50, sizeof(void*)*2, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*2 + 4, x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint32_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_27, 0);
lean_inc(x_53);
lean_dec(x_27);
x_54 = lean_ctor_get(x_26, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_55 = x_26;
} else {
 lean_dec_ref(x_26);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = 0;
x_60 = 1;
x_61 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set_uint32(x_61, sizeof(void*)*2, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 4, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
return x_26;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Simp_getConfig___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 10);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_simpArith___lambda__2(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
lean_dec(x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpArith___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpArith___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_mkCongrFun(x_3, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_box(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_mkCongr(x_3, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_box(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
lean_dec(x_3);
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_array_get_size(x_2);
x_32 = lean_nat_dec_lt(x_4, x_31);
lean_dec(x_31);
x_33 = lean_array_get_size(x_1);
x_34 = lean_nat_dec_lt(x_4, x_33);
lean_dec(x_33);
if (x_32 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = l_Lean_instInhabitedExpr;
x_205 = l___private_Init_Util_0__outOfBounds___rarg(x_204);
x_35 = x_205;
goto block_203;
}
else
{
lean_object* x_206; 
x_206 = lean_array_fget(x_2, x_4);
x_35 = x_206;
goto block_203;
}
block_28:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_26;
x_7 = x_25;
x_15 = x_22;
goto _start;
}
}
block_203:
{
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_37 = lean_infer_type(x_36, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_40 = l_Lean_Meta_whnfD(x_38, x_11, x_12, x_13, x_14, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_isArrow(x_41);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
x_44 = lean_dsimp(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_expr_eqv(x_45, x_35);
lean_dec(x_35);
if (x_47 == 0)
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_29);
x_48 = 1;
x_49 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_50 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(x_45, x_48, x_30, x_49, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_21 = x_51;
x_22 = x_52;
goto block_28;
}
else
{
uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_57 = lean_box(0);
x_58 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_59 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(x_45, x_58, x_30, x_57, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_21 = x_60;
x_22 = x_61;
goto block_28;
}
else
{
uint8_t x_62; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_59);
if (x_62 == 0)
{
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_44);
if (x_66 == 0)
{
return x_44;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_44, 0);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_44);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
x_70 = lean_simp(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_42);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_expr_eqv(x_73, x_35);
lean_dec(x_35);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_29);
x_75 = 1;
x_76 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_77 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_71, x_75, x_30, x_76, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_21 = x_78;
x_22 = x_79;
goto block_28;
}
else
{
uint8_t x_80; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_84 = lean_box(0);
x_85 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_86 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_71, x_85, x_30, x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_72);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_21 = x_87;
x_22 = x_88;
goto block_28;
}
else
{
uint8_t x_89; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_89 = !lean_is_exclusive(x_86);
if (x_89 == 0)
{
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_70, 0);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_97 = !lean_is_exclusive(x_40);
if (x_97 == 0)
{
return x_40;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_101 = !lean_is_exclusive(x_37);
if (x_101 == 0)
{
return x_37;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_37, 0);
x_103 = lean_ctor_get(x_37, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_37);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_array_fget(x_1, x_4);
x_106 = lean_ctor_get_uint8(x_105, sizeof(void*)*1 + 1);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
x_107 = lean_simp(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_expr_eqv(x_110, x_35);
lean_dec(x_35);
lean_dec(x_110);
if (x_111 == 0)
{
uint8_t x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_29);
x_112 = 1;
x_113 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_114 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_108, x_112, x_30, x_113, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_109);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_21 = x_115;
x_22 = x_116;
goto block_28;
}
else
{
uint8_t x_117; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_114);
if (x_117 == 0)
{
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_114);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_121 = lean_box(0);
x_122 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_123 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_108, x_122, x_30, x_121, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_109);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_21 = x_124;
x_22 = x_125;
goto block_28;
}
else
{
uint8_t x_126; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_126 = !lean_is_exclusive(x_123);
if (x_126 == 0)
{
return x_123;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_123, 0);
x_128 = lean_ctor_get(x_123, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_123);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_130 = !lean_is_exclusive(x_107);
if (x_130 == 0)
{
return x_107;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_107, 0);
x_132 = lean_ctor_get(x_107, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_107);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_30, 0);
lean_inc(x_134);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_135 = lean_infer_type(x_134, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_138 = l_Lean_Meta_whnfD(x_136, x_11, x_12, x_13, x_14, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Expr_isArrow(x_139);
lean_dec(x_139);
if (x_141 == 0)
{
lean_object* x_142; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
x_142 = lean_dsimp(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_expr_eqv(x_143, x_35);
lean_dec(x_35);
if (x_145 == 0)
{
uint8_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_29);
x_146 = 1;
x_147 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_148 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(x_143, x_146, x_30, x_147, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_144);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_21 = x_149;
x_22 = x_150;
goto block_28;
}
else
{
uint8_t x_151; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_151 = !lean_is_exclusive(x_148);
if (x_151 == 0)
{
return x_148;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_148, 0);
x_153 = lean_ctor_get(x_148, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_148);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_155 = lean_box(0);
x_156 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_157 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(x_143, x_156, x_30, x_155, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_144);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_21 = x_158;
x_22 = x_159;
goto block_28;
}
else
{
uint8_t x_160; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_160 = !lean_is_exclusive(x_157);
if (x_160 == 0)
{
return x_157;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_157, 0);
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_157);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_164 = !lean_is_exclusive(x_142);
if (x_164 == 0)
{
return x_142;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_142, 0);
x_166 = lean_ctor_get(x_142, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_142);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
lean_object* x_168; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_35);
x_168 = lean_simp(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_140);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_expr_eqv(x_171, x_35);
lean_dec(x_35);
lean_dec(x_171);
if (x_172 == 0)
{
uint8_t x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_29);
x_173 = 1;
x_174 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_175 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_169, x_173, x_30, x_174, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_170);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_21 = x_176;
x_22 = x_177;
goto block_28;
}
else
{
uint8_t x_178; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_178 = !lean_is_exclusive(x_175);
if (x_178 == 0)
{
return x_175;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_175, 0);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_175);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
lean_object* x_182; uint8_t x_183; lean_object* x_184; 
x_182 = lean_box(0);
x_183 = lean_unbox(x_29);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_184 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_169, x_183, x_30, x_182, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_170);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_21 = x_185;
x_22 = x_186;
goto block_28;
}
else
{
uint8_t x_187; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_184, 0);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_184);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_191 = !lean_is_exclusive(x_168);
if (x_191 == 0)
{
return x_168;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_168, 0);
x_193 = lean_ctor_get(x_168, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_168);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_195 = !lean_is_exclusive(x_138);
if (x_195 == 0)
{
return x_138;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_138, 0);
x_197 = lean_ctor_get(x_138, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_138);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_199 = !lean_is_exclusive(x_135);
if (x_199 == 0)
{
return x_135;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_135, 0);
x_201 = lean_ctor_get(x_135, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_135);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
}
}
else
{
lean_object* x_207; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_7);
lean_ctor_set(x_207, 1, x_15);
return x_207;
}
}
else
{
lean_object* x_208; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_7);
lean_ctor_set(x_208, 1, x_15);
return x_208;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_5, x_4);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
lean_dec(x_3);
x_21 = lean_nat_dec_lt(x_4, x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_instInhabitedExpr;
x_23 = l___private_Init_Util_0__outOfBounds___rarg(x_22);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_24 = l_Lean_Meta_Simp_mkCongrFun(x_7, x_23, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_27;
x_7 = x_25;
x_15 = x_26;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_array_fget(x_1, x_4);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_34 = l_Lean_Meta_Simp_mkCongrFun(x_7, x_33, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_20;
x_4 = x_37;
x_7 = x_35;
x_15 = x_36;
goto _start;
}
else
{
uint8_t x_39; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_15);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_15);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_13);
x_15 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2(x_1, x_13, x_13, x_2, x_13, x_14, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_15);
lean_dec(x_2);
lean_inc(x_16);
x_17 = l_Lean_Expr_stripArgsN(x_3, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
lean_inc(x_17);
x_18 = l_Lean_Meta_getFunInfoNArgs(x_17, x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1;
lean_inc(x_16);
x_23 = lean_mk_array(x_16, x_22);
x_24 = l_Lean_Expr_getAppArgsN_loop(x_16, x_3, x_23);
x_25 = lean_box(0);
x_26 = 0;
x_27 = 1;
x_28 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set_uint32(x_28, sizeof(void*)*2, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*2 + 4, x_27);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_34 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1(x_21, x_24, x_29, x_33, x_29, x_14, x_32, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_35);
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_34, 0);
lean_dec(x_39);
lean_ctor_set(x_34, 0, x_25);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_25);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_dec(x_34);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_dec(x_35);
x_44 = lean_box(0);
x_45 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1(x_24, x_29, x_43, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_24);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_34, 0);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_34);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_11);
x_13 = l_Lean_Meta_Match_MatcherInfo_arity(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2(x_1, x_12, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_17);
x_18 = l_Lean_Meta_isRflTheorem(x_17, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_17);
x_22 = l_Lean_Expr_const___override(x_17, x_21);
x_23 = 1;
x_24 = 0;
x_25 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_24);
x_26 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_27 = lean_unsigned_to_nat(1000u);
x_28 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_23);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 1, x_24);
x_29 = lean_unbox(x_19);
lean_dec(x_19);
lean_ctor_set_uint8(x_28, sizeof(void*)*5 + 2, x_29);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_10, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_10, 4);
lean_inc(x_34);
x_35 = lean_ctor_get(x_10, 5);
lean_inc(x_35);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 2;
lean_ctor_set_uint8(x_30, 9, x_37);
x_38 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_31);
lean_ctor_set(x_38, 2, x_32);
lean_ctor_set(x_38, 3, x_33);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_39 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_28, x_7, x_8, x_9, x_38, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
x_43 = lean_usize_add(x_5, x_42);
lean_inc(x_2);
{
size_t _tmp_4 = x_43;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_13 = x_41;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_14 = _tmp_13;
}
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_39, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_40, 0, x_49);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_39, 0, x_51);
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_39, 0, x_56);
return x_39;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_ctor_get(x_40, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_59 = x_40;
} else {
 lean_dec_ref(x_40);
 x_59 = lean_box(0);
}
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_57);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_39);
if (x_65 == 0)
{
return x_39;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_39, 0);
x_67 = lean_ctor_get(x_39, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_39);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_69 = lean_ctor_get_uint8(x_30, 0);
x_70 = lean_ctor_get_uint8(x_30, 1);
x_71 = lean_ctor_get_uint8(x_30, 2);
x_72 = lean_ctor_get_uint8(x_30, 3);
x_73 = lean_ctor_get_uint8(x_30, 4);
x_74 = lean_ctor_get_uint8(x_30, 5);
x_75 = lean_ctor_get_uint8(x_30, 6);
x_76 = lean_ctor_get_uint8(x_30, 7);
x_77 = lean_ctor_get_uint8(x_30, 8);
x_78 = lean_ctor_get_uint8(x_30, 10);
x_79 = lean_ctor_get_uint8(x_30, 11);
lean_dec(x_30);
x_80 = 2;
x_81 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_81, 0, x_69);
lean_ctor_set_uint8(x_81, 1, x_70);
lean_ctor_set_uint8(x_81, 2, x_71);
lean_ctor_set_uint8(x_81, 3, x_72);
lean_ctor_set_uint8(x_81, 4, x_73);
lean_ctor_set_uint8(x_81, 5, x_74);
lean_ctor_set_uint8(x_81, 6, x_75);
lean_ctor_set_uint8(x_81, 7, x_76);
lean_ctor_set_uint8(x_81, 8, x_77);
lean_ctor_set_uint8(x_81, 9, x_80);
lean_ctor_set_uint8(x_81, 10, x_78);
lean_ctor_set_uint8(x_81, 11, x_79);
x_82 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_31);
lean_ctor_set(x_82, 2, x_32);
lean_ctor_set(x_82, 3, x_33);
lean_ctor_set(x_82, 4, x_34);
lean_ctor_set(x_82, 5, x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_83 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_28, x_7, x_8, x_9, x_82, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; size_t x_86; size_t x_87; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = 1;
x_87 = lean_usize_add(x_5, x_86);
lean_inc(x_2);
{
size_t _tmp_4 = x_87;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_13 = x_85;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_14 = _tmp_13;
}
goto _start;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_90 = x_83;
} else {
 lean_dec_ref(x_83);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_91);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_90)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_90;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_89);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_83, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_100 = x_83;
} else {
 lean_dec_ref(x_83);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_18);
if (x_102 == 0)
{
return x_18;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_18, 0);
x_104 = lean_ctor_get(x_18, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_18);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_get_match_equations_for(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_get_size(x_14);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore___spec__1(x_2, x_19, x_14, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Simp_simpMatchCore___lambda__1(x_15, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_11, 0);
x_38 = lean_ctor_get(x_11, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_11);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore___spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpMatchCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_13, x_1);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(x_17, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_simpMatchCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch___spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_23 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(x_22, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Simp_simpMatchCore(x_12, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_23, 0, x_30);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_10);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_Simp_simpMatch___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_11, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_box(0);
x_20 = 0;
x_21 = 1;
x_22 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint32(x_22, sizeof(void*)*2, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 4, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_11, 0, x_23);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint32_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_box(0);
x_27 = 0;
x_28 = 1;
x_29 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set_uint32(x_29, sizeof(void*)*2, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2 + 4, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_11);
if (x_32 == 0)
{
return x_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_11, 0);
x_34 = lean_ctor_get(x_11, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_11);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Simp_getConfig___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 7);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_simpMatch___lambda__3(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_simpMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpMatch___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pre", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_18 = lean_array_uget(x_4, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 4);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_22 = l_Lean_Meta_Simp_rewrite_x3f(x_2, x_19, x_20, x_21, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
lean_inc(x_3);
{
size_t _tmp_5 = x_26;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_14 = x_24;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_23, 0, x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
return x_22;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_array_get_size(x_11);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(x_1, x_2, x_16, x_11, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_simpMatchCore___lambda__1(x_12, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(x_16, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_Simp_rewritePre(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("post", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_6, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_18 = lean_array_uget(x_4, x_6);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 4);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_22 = l_Lean_Meta_Simp_rewrite_x3f(x_2, x_19, x_20, x_21, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_usize_add(x_6, x_25);
lean_inc(x_3);
{
size_t _tmp_5 = x_26;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_14 = x_24;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_22, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_23, 0, x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_23);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_23, 0);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_22, 0, x_39);
return x_22;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_42 = x_23;
} else {
 lean_dec_ref(x_23);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_22);
if (x_48 == 0)
{
return x_22;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_22, 0);
x_50 = lean_ctor_get(x_22, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_22);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_box(0);
x_13 = lean_array_get_size(x_11);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(x_1, x_2, x_16, x_11, x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Meta_Simp_simpMatchCore___lambda__1(x_12, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
return x_17;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(x_16, x_2, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_Simp_rewritePost(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = lean_simp(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Lean_Expr_isTrue(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; 
lean_free_object(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_Simp_Result_getProof(x_13, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
x_21 = l_Lean_Meta_mkOfEqTrue(x_19, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = l_Lean_Exception_isRuntime(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_8);
x_32 = lean_box(0);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
uint8_t x_33; 
x_33 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; 
lean_dec(x_30);
x_34 = lean_box(0);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = l_Lean_Exception_isRuntime(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_8);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_35);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_44 = !lean_is_exclusive(x_18);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = l_Lean_Exception_isRuntime(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_8);
x_47 = lean_box(0);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_47);
return x_18;
}
else
{
uint8_t x_48; 
x_48 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; 
lean_dec(x_45);
x_49 = lean_box(0);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_49);
return x_18;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = l_Lean_Exception_isRuntime(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_50);
lean_dec(x_8);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_50);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_11, 0);
x_60 = lean_ctor_get(x_11, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_11);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = l_Lean_Expr_isTrue(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = l_Lean_Meta_Simp_Result_getProof(x_59, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_8);
x_68 = l_Lean_Meta_mkOfEqTrue(x_66, x_6, x_7, x_8, x_9, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_8);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_69);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Exception_isRuntime(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_74);
lean_dec(x_8);
x_78 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
 lean_ctor_set_tag(x_79, 0);
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_80 == 0)
{
lean_object* x_81; 
if (lean_is_scalar(x_76)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_76;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_74);
x_82 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_76;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_75);
return x_83;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_84 = lean_ctor_get(x_65, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_86 = x_65;
} else {
 lean_dec_ref(x_65);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Exception_isRuntime(x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_84);
lean_dec(x_8);
x_88 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
 lean_ctor_set_tag(x_89, 0);
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
lean_dec(x_8);
if (x_90 == 0)
{
lean_object* x_91; 
if (lean_is_scalar(x_86)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_86;
}
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_85);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_84);
x_92 = lean_box(0);
if (lean_is_scalar(x_86)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_86;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_85);
return x_93;
}
}
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_94 = !lean_is_exclusive(x_11);
if (x_94 == 0)
{
return x_11;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_11, 0);
x_96 = lean_ctor_get(x_11, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_11);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeGround___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(">> discharge\?: ", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeGround___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_dischargeGround___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_11 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_Simp_dischargeGround___lambda__1(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_1);
x_18 = l_Lean_MessageData_ofExpr(x_1);
x_19 = l_Lean_Meta_Simp_dischargeGround___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_10, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Simp_dischargeGround___lambda__1(x_1, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_24);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeGround___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_dischargeGround___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ground", 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
x_2 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
x_3 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unfolded, ", 10);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; 
lean_dec(x_6);
x_17 = lean_array_uget(x_3, x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_17);
x_27 = l_Lean_Meta_isRflTheorem(x_17, x_12, x_13, x_14);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
lean_inc(x_17);
x_31 = l_Lean_Expr_const___override(x_17, x_30);
x_32 = 1;
x_33 = 0;
x_34 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1 + 1, x_33);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_36 = lean_unsigned_to_nat(1000u);
x_37 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_36);
lean_ctor_set(x_37, 4, x_34);
lean_ctor_set_uint8(x_37, sizeof(void*)*5, x_32);
lean_ctor_set_uint8(x_37, sizeof(void*)*5 + 1, x_33);
x_38 = lean_unbox(x_28);
lean_dec(x_28);
lean_ctor_set_uint8(x_37, sizeof(void*)*5 + 2, x_38);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_39 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_29);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_2);
x_18 = x_42;
x_19 = x_41;
goto block_26;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2;
x_46 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_43);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1(x_44, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_49);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_18 = x_52;
x_19 = x_53;
goto block_26;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
lean_inc(x_1);
x_55 = l_Lean_MessageData_ofExpr(x_1);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__4;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
x_61 = l_Lean_MessageData_ofExpr(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_45, x_64, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_54);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1(x_44, x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
lean_dec(x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_18 = x_69;
x_19 = x_70;
goto block_26;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_39);
if (x_71 == 0)
{
return x_39;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_39, 0);
x_73 = lean_ctor_get(x_39, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_39);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_27);
if (x_75 == 0)
{
return x_27;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_27, 0);
x_77 = lean_ctor_get(x_27, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_27);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
block_26:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_22;
x_14 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_box(0);
x_12 = 0;
x_13 = 1;
x_14 = lean_alloc_ctor(0, 2, 5);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set_uint32(x_14, sizeof(void*)*2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2 + 4, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
static lean_object* _init_l_Lean_Meta_Simp_sevalGround___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("delta, ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_sevalGround___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_sevalGround___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
x_13 = l_Lean_Core_instantiateValueLevelParams(x_1, x_2, x_10, x_11, x_12);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_16);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_dec(x_17);
lean_inc(x_3);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_3, x_18);
x_20 = 1;
x_21 = 0;
x_22 = l_Lean_Expr_betaRev(x_14, x_19, x_20, x_21);
lean_dec(x_19);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Simp_sevalGround___lambda__1(x_22, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_MessageData_ofExpr(x_3);
x_32 = l_Lean_Meta_Simp_sevalGround___lambda__2___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_22);
x_36 = l_Lean_MessageData_ofExpr(x_22);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_23, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_Simp_sevalGround___lambda__1(x_22, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_42);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
return x_13;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_13, 0);
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_4);
x_13 = l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_ConstantInfo_hasValue(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_ConstantInfo_levelParams(x_15);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_List_lengthTRAux___rarg(x_19, x_20);
lean_dec(x_19);
x_22 = l_List_lengthTRAux___rarg(x_2, x_20);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_24 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_13);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_Simp_sevalGround___lambda__2(x_15, x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = l_Lean_ConstantInfo_hasValue(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_30 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = l_Lean_ConstantInfo_levelParams(x_27);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_List_lengthTRAux___rarg(x_32, x_33);
lean_dec(x_32);
x_35 = l_List_lengthTRAux___rarg(x_2, x_33);
x_36 = lean_nat_dec_eq(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_27);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_37 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(0);
x_40 = l_Lean_Meta_Simp_sevalGround___lambda__2(x_27, x_2, x_3, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_40;
}
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_dec(x_4);
x_13 = l_Lean_Expr_isConst(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Meta_Simp_sevalGround___lambda__3(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_16 = lean_infer_type(x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_Meta_whnfD(x_17, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
uint8_t x_21; 
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_20);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_Simp_sevalGround___lambda__3(x_1, x_2, x_3, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_19);
if (x_30 == 0)
{
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_13, 0);
x_15 = lean_ctor_get_uint8(x_13, 1);
x_16 = lean_ctor_get_uint8(x_13, 2);
x_17 = lean_ctor_get_uint8(x_13, 3);
x_18 = lean_ctor_get_uint8(x_13, 4);
x_19 = lean_ctor_get_uint8(x_13, 5);
x_20 = lean_ctor_get_uint8(x_13, 6);
x_21 = lean_ctor_get_uint8(x_13, 7);
x_22 = lean_ctor_get_uint8(x_13, 8);
x_23 = lean_ctor_get_uint8(x_13, 10);
x_24 = lean_ctor_get_uint8(x_13, 11);
lean_dec(x_13);
x_25 = 1;
x_26 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_26, 0, x_14);
lean_ctor_set_uint8(x_26, 1, x_15);
lean_ctor_set_uint8(x_26, 2, x_16);
lean_ctor_set_uint8(x_26, 3, x_17);
lean_ctor_set_uint8(x_26, 4, x_18);
lean_ctor_set_uint8(x_26, 5, x_19);
lean_ctor_set_uint8(x_26, 6, x_20);
lean_ctor_set_uint8(x_26, 7, x_21);
lean_ctor_set_uint8(x_26, 8, x_22);
lean_ctor_set_uint8(x_26, 9, x_25);
lean_ctor_set_uint8(x_26, 10, x_23);
lean_ctor_set_uint8(x_26, 11, x_24);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_8, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 3);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 4);
lean_inc(x_30);
x_31 = lean_ctor_get(x_8, 5);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_28);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_30);
lean_ctor_set(x_32, 5, x_31);
x_33 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_34 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_33, x_32, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_Simp_sevalGround___lambda__4(x_1, x_2, x_3, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_box(0);
x_42 = lean_array_get_size(x_40);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_46 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1(x_3, x_45, x_40, x_43, x_44, x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_39);
lean_dec(x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_box(0);
x_51 = l_Lean_Meta_Simp_simpMatchCore___lambda__1(x_41, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_49);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_46, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_54);
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
lean_dec(x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_34);
if (x_62 == 0)
{
return x_34;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_34, 0);
x_64 = lean_ctor_get(x_34, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_34);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
lean_inc(x_1);
x_13 = l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Simp_sevalGround___lambda__5(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = 1;
x_16 = 0;
lean_inc(x_12);
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_16);
x_18 = l_Lean_Meta_SimpTheoremsArray_isErased(x_14, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Meta_Simp_sevalGround___lambda__6(x_12, x_13, x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasExprMVar(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasFVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Meta_Simp_sevalGround___lambda__7(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1(x_1, x_2, x_3, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_sevalGround___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_sevalGround___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_preSEval___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpMatch), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_userPreSimprocs), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Simp_preSEval___lambda__1___closed__1;
x_13 = l_Lean_Meta_Simp_andThen(x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Simp_preSEval___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewritePre___boxed), 10, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preSEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preSEval___lambda__1), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Simp_preSEval___closed__1;
x_13 = l_Lean_Meta_Simp_andThen(x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postSEval___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_sevalGround), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postSEval___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpCtorEq), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postSEval___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_postSEval___lambda__1___closed__1;
x_2 = l_Lean_Meta_Simp_postSEval___lambda__1___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_andThen), 11, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Simp_postSEval___lambda__1___closed__3;
x_12 = l_Lean_Meta_Simp_andThen(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postSEval___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewritePost___boxed), 10, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postSEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_userPostSimprocs), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postSEval___lambda__1), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Simp_postSEval___closed__1;
x_14 = l_Lean_Meta_Simp_andThen(x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeGround), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_Simp_getSEvalSimprocs___rarg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_7 = lean_array_push(x_6, x_5);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preSEval), 10, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postSEval), 10, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1;
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_15 = lean_array_push(x_14, x_12);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preSEval), 10, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postSEval), 10, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSEvalMethods___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_mkSEvalMethods___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalMethods___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_mkSEvalMethods(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSEvalContext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_sevalSimpExtension;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkSEvalContext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 16);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
return x_6;
}
}
static uint32_t _init_l_Lean_Meta_Simp_mkSEvalContext___closed__3() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l_Lean_Meta_Simp_mkSEvalContext___closed__1;
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_4, x_1, x_2, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_getSimpCongrTheorems___rarg(x_2, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_12 = lean_array_push(x_11, x_6);
x_13 = lean_box(0);
x_14 = 0;
x_15 = l_Lean_Meta_Simp_mkSEvalContext___closed__2;
x_16 = l_Lean_Meta_Simp_mkSEvalContext___closed__3;
x_17 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_10);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set_uint32(x_17, sizeof(void*)*4, x_16);
lean_ctor_set_uint32(x_17, sizeof(void*)*4 + 4, x_14);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; lean_object* x_24; uint32_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_20 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_21 = lean_array_push(x_20, x_6);
x_22 = lean_box(0);
x_23 = 0;
x_24 = l_Lean_Meta_Simp_mkSEvalContext___closed__2;
x_25 = l_Lean_Meta_Simp_mkSEvalContext___closed__3;
x_26 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint32(x_26, sizeof(void*)*4, x_25);
lean_ctor_set_uint32(x_26, sizeof(void*)*4 + 4, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSEvalContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_mkSEvalContext(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Simp_seval___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_10 = l_Lean_Meta_Simp_mkSEvalMethods___rarg(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_Simp_mkSEvalContext(x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_4, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_4, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_25, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = l_Lean_Meta_Simp_seval___closed__1;
lean_ctor_set(x_25, 2, x_30);
lean_ctor_set(x_25, 0, x_30);
x_31 = lean_st_ref_set(x_4, x_25, x_26);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_4);
x_33 = lean_simp(x_1, x_11, x_14, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_take(x_4, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_37, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_37, 0);
lean_dec(x_41);
lean_ctor_set(x_37, 2, x_23);
lean_ctor_set(x_37, 0, x_19);
x_42 = lean_st_ref_set(x_4, x_37, x_38);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_34);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_37, 1);
x_48 = lean_ctor_get(x_37, 3);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_19);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_23);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_st_ref_set(x_4, x_49, x_38);
lean_dec(x_4);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_33, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_33, 1);
lean_inc(x_55);
lean_dec(x_33);
x_56 = lean_st_ref_take(x_4, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 2);
lean_dec(x_60);
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
lean_ctor_set(x_57, 2, x_23);
lean_ctor_set(x_57, 0, x_19);
x_62 = lean_st_ref_set(x_4, x_57, x_58);
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_54);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_57, 1);
x_68 = lean_ctor_get(x_57, 3);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_57);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_19);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_23);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_st_ref_set(x_4, x_69, x_58);
lean_dec(x_4);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_54);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_25, 1);
x_75 = lean_ctor_get(x_25, 3);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_25);
x_76 = l_Lean_Meta_Simp_seval___closed__1;
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_75);
x_78 = lean_st_ref_set(x_4, x_77, x_26);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
lean_inc(x_4);
x_80 = lean_simp(x_1, x_11, x_14, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_st_ref_take(x_4, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 3);
lean_inc(x_87);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 x_88 = x_84;
} else {
 lean_dec_ref(x_84);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 4, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_19);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_89, 2, x_23);
lean_ctor_set(x_89, 3, x_87);
x_90 = lean_st_ref_set(x_4, x_89, x_85);
lean_dec(x_4);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_81);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_ctor_get(x_80, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
lean_dec(x_80);
x_96 = lean_st_ref_take(x_4, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 3);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(0, 4, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_19);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_23);
lean_ctor_set(x_102, 3, x_100);
x_103 = lean_st_ref_set(x_4, x_102, x_98);
lean_dec(x_4);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
 lean_ctor_set_tag(x_106, 1);
}
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_seval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_seval(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__2;
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_st_ref_take(x_1, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_8, 3);
lean_dec(x_11);
x_12 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3;
lean_ctor_set(x_8, 3, x_12);
x_13 = lean_st_ref_set(x_1, x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_6);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 2);
x_21 = lean_ctor_get(x_8, 4);
x_22 = lean_ctor_get(x_8, 5);
x_23 = lean_ctor_get(x_8, 6);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_24 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3;
x_25 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
lean_ctor_set(x_25, 4, x_21);
lean_ctor_set(x_25, 5, x_22);
lean_ctor_set(x_25, 6, x_23);
x_26 = lean_st_ref_set(x_1, x_25, x_9);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___boxed), 2, 0);
return x_7;
}
}
static double _init_l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1000000000u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_io_mono_nanos_now(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_io_mono_nanos_now(x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; double x_22; double x_23; double x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_nat_sub(x_18, x_11);
lean_dec(x_11);
lean_dec(x_18);
x_20 = 0;
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Float_ofScientific(x_19, x_20, x_21);
lean_dec(x_19);
x_23 = l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3___closed__1;
x_24 = lean_float_div(x_22, x_23);
x_25 = lean_box_float(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; double x_32; double x_33; double x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_nat_sub(x_27, x_11);
lean_dec(x_11);
lean_dec(x_27);
x_30 = 0;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Float_ofScientific(x_29, x_30, x_31);
lean_dec(x_29);
x_33 = l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3___closed__1;
x_34 = lean_float_div(x_32, x_33);
x_35 = lean_box_float(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_28);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_st_ref_take(x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_15, 3);
x_19 = l_Lean_PersistentArray_toArray___rarg(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___spec__1(x_21, x_22, x_19);
x_24 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_PersistentArray_push___rarg(x_1, x_25);
lean_ctor_set(x_15, 3, x_26);
x_27 = lean_st_ref_set(x_12, x_15, x_16);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
x_36 = lean_ctor_get(x_15, 2);
x_37 = lean_ctor_get(x_15, 3);
x_38 = lean_ctor_get(x_15, 4);
x_39 = lean_ctor_get(x_15, 5);
x_40 = lean_ctor_get(x_15, 6);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_41 = l_Lean_PersistentArray_toArray___rarg(x_37);
x_42 = lean_array_get_size(x_41);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = 0;
x_45 = l_Array_mapMUnsafe_map___at___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___spec__1(x_43, x_44, x_41);
x_46 = lean_alloc_ctor(9, 3, 1);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_4);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_5);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_PersistentArray_push___rarg(x_1, x_47);
x_49 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set(x_49, 2, x_36);
lean_ctor_set(x_49, 3, x_48);
lean_ctor_set(x_49, 4, x_38);
lean_ctor_set(x_49, 5, x_39);
lean_ctor_set(x_49, 6, x_40);
x_50 = lean_st_ref_set(x_12, x_49, x_16);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_simpGround___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_11, 5);
x_16 = l_Lean_replaceRef(x_3, x_15);
lean_dec(x_15);
lean_ctor_set(x_11, 5, x_16);
x_17 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_4, x_9, x_10, x_11, x_12, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
x_23 = lean_ctor_get(x_11, 2);
x_24 = lean_ctor_get(x_11, 3);
x_25 = lean_ctor_get(x_11, 4);
x_26 = lean_ctor_get(x_11, 5);
x_27 = lean_ctor_get(x_11, 6);
x_28 = lean_ctor_get(x_11, 7);
x_29 = lean_ctor_get(x_11, 8);
x_30 = lean_ctor_get(x_11, 9);
x_31 = lean_ctor_get(x_11, 10);
x_32 = lean_ctor_get_uint8(x_11, sizeof(void*)*11);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_33 = l_Lean_replaceRef(x_3, x_26);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_22);
lean_ctor_set(x_34, 2, x_23);
lean_ctor_set(x_34, 3, x_24);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set(x_34, 5, x_33);
lean_ctor_set(x_34, 6, x_27);
lean_ctor_set(x_34, 7, x_28);
lean_ctor_set(x_34, 8, x_29);
lean_ctor_set(x_34, 9, x_30);
lean_ctor_set(x_34, 10, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*11, x_32);
x_35 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_4, x_9, x_10, x_34, x_12, x_13);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5(x_1, x_2, x_3, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_34, x_12, x_37);
lean_dec(x_34);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = l_Lean_Exception_isRuntime(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
uint8_t x_22; 
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
lean_dec(x_7);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = l_Lean_Exception_isRuntime(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_7, sizeof(void*)*11);
lean_dec(x_7);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_24);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_inc(x_13);
x_16 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_simpGround___spec__4(x_1, x_2, x_3, x_6, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
lean_dec(x_13);
lean_dec(x_9);
return x_18;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_profiler;
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("s] ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, double x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__1;
x_20 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_6, x_19);
lean_dec(x_6);
if (x_20 == 0)
{
if (x_7 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_10, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_15);
lean_dec(x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = lean_float_to_string(x_8);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
x_31 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_box(0);
x_34 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_32, x_33, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_15);
lean_dec(x_13);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_float_to_string(x_8);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
x_43 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_44, x_45, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_15);
lean_dec(x_13);
return x_46;
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<exception thrown while producing trace node message>", 53);
return x_1;
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, double x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_19 = lean_ctor_get(x_16, 5);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
x_20 = lean_apply_9(x_8, x_4, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_22);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
x_27 = l_Lean_Exception_isRuntime(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_20);
lean_dec(x_25);
x_28 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2;
x_29 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_28, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_26);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = lean_ctor_get_uint8(x_16, sizeof(void*)*11);
if (x_30 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_20);
lean_dec(x_25);
x_31 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2;
x_32 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_31, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_26);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
x_35 = l_Lean_Exception_isRuntime(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_33);
x_36 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2;
x_37 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_36, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_ctor_get_uint8(x_16, sizeof(void*)*11);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_33);
x_40 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2;
x_41 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7, lean_box(0), x_40, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_34);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_4);
return x_41;
}
}
}
}
}
}
static lean_object* _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_trace_profiler;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_17 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg(x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__1), 9, 1);
lean_closure_set(x_20, 0, x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3(x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_71; uint8_t x_72; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_71 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1;
x_72 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_4, x_71);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = 0;
x_26 = x_73;
goto block_70;
}
else
{
double x_74; double x_75; uint8_t x_76; 
x_74 = l_Lean_trace_profiler_threshold_getSecs(x_4);
x_75 = lean_unbox_float(x_25);
x_76 = lean_float_decLt(x_74, x_75);
x_26 = x_76;
goto block_70;
}
block_70:
{
if (x_6 == 0)
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_st_ref_take(x_15, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_28, 3);
x_32 = l_Lean_PersistentArray_append___rarg(x_18, x_31);
lean_ctor_set(x_28, 3, x_32);
x_33 = lean_st_ref_set(x_15, x_28, x_29);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_24);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_28, 0);
x_45 = lean_ctor_get(x_28, 1);
x_46 = lean_ctor_get(x_28, 2);
x_47 = lean_ctor_get(x_28, 3);
x_48 = lean_ctor_get(x_28, 4);
x_49 = lean_ctor_get(x_28, 5);
x_50 = lean_ctor_get(x_28, 6);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_28);
x_51 = l_Lean_PersistentArray_append___rarg(x_18, x_47);
x_52 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_52, 0, x_44);
lean_ctor_set(x_52, 1, x_45);
lean_ctor_set(x_52, 2, x_46);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
x_53 = lean_st_ref_set(x_15, x_52, x_29);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6(x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_54);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_24);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
else
{
lean_object* x_64; double x_65; lean_object* x_66; 
x_64 = lean_box(0);
x_65 = lean_unbox_float(x_25);
lean_dec(x_25);
x_66 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4(x_18, x_2, x_3, x_24, x_4, x_26, x_65, x_5, lean_box(0), x_64, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
return x_66;
}
}
else
{
lean_object* x_67; double x_68; lean_object* x_69; 
x_67 = lean_box(0);
x_68 = lean_unbox_float(x_25);
lean_dec(x_25);
x_69 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4(x_18, x_2, x_3, x_24, x_4, x_26, x_68, x_5, lean_box(0), x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_23);
return x_69;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_21);
if (x_77 == 0)
{
return x_21;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_21, 0);
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_21);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1;
x_19 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_apply_8(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_box(0);
x_30 = lean_unbox(x_15);
lean_dec(x_15);
x_31 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5(x_3, x_1, x_4, x_13, x_2, x_30, lean_box(0), x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_box(0);
x_34 = lean_unbox(x_15);
lean_dec(x_15);
x_35 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5(x_3, x_1, x_4, x_13, x_2, x_34, lean_box(0), x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_35;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpGround___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("seval: ", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_simpGround___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_simpGround___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_MessageData_ofExpr(x_1);
x_13 = l_Lean_Meta_Simp_simpGround___lambda__1___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Exception_toMessageData(x_11);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_MessageData_ofExpr(x_1);
x_24 = l_Lean_Meta_Simp_simpGround___lambda__1___closed__2;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
lean_dec(x_22);
x_29 = l_Lean_MessageData_ofExpr(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpGround___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_seval___boxed), 9, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2;
x_14 = 1;
x_15 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1(x_13, x_11, x_12, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_3);
x_12 = l_Lean_Meta_isMatcher___at_Lean_Meta_Simp_mkCongrSimp_x3f___spec__10(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Simp_simpGround___lambda__2(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = 1;
x_15 = 0;
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1 + 1, x_15);
x_17 = l_Lean_Meta_SimpTheoremsArray_isErased(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Meta_Simp_simpGround___lambda__3(x_12, x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_22 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = l_Lean_Expr_hasExprMVar(x_1);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasFVar(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Simp_simpGround___lambda__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_Simp_getConfig___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*2 + 14);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_Simp_simpCtorEq___closed__3;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_Simp_simpGround___lambda__5(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Util_Trace_0__Lean_addTraceNodeCore___at_Lean_Meta_Simp_simpGround___spec__5(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_simpGround___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at_Lean_Meta_Simp_simpGround___spec__4(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_MonadExcept_ofExcept___at_Lean_Meta_Simp_simpGround___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__2(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; double x_21; lean_object* x_22; 
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox(x_7);
lean_dec(x_7);
x_21 = lean_unbox_float(x_8);
lean_dec(x_8);
x_22 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3(x_1, x_2, x_3, x_19, x_5, x_6, x_20, x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; uint8_t x_20; double x_21; lean_object* x_22; 
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = lean_unbox_float(x_7);
lean_dec(x_7);
x_22 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4(x_1, x_2, x_19, x_4, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5(x_1, x_2, x_17, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpGround___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpGround___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpGround___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Simp_preDefault___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpUsingDecide), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_userPreSimprocs), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Simp_preDefault___lambda__1___closed__1;
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_andThen), 11, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_Simp_preSEval___lambda__1___closed__1;
x_15 = l_Lean_Meta_Simp_andThen(x_14, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_preDefault___lambda__1), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = l_Lean_Meta_Simp_preSEval___closed__1;
x_13 = l_Lean_Meta_Simp_andThen(x_12, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postDefault___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_postSEval___lambda__1___closed__2;
x_2 = l_Lean_Meta_Simp_preDefault___lambda__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_andThen), 11, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postDefault___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpArith), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_Simp_postDefault___lambda__1___closed__2;
x_11 = l_Lean_Meta_Simp_postDefault___lambda__1___closed__1;
x_12 = l_Lean_Meta_Simp_andThen(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postDefault___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_simpGround), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postDefault___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postDefault___lambda__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_Simp_postDefault___lambda__2___closed__1;
x_11 = l_Lean_Meta_Simp_postDefault___lambda__2___closed__2;
x_12 = l_Lean_Meta_Simp_andThen(x_10, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Simp_postDefault___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postDefault___lambda__2), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Simp_postDefault___lambda__3___closed__1;
x_12 = l_Lean_Meta_Simp_andThen(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_userPostSimprocs), 10, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_postDefault___lambda__3), 10, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_Simp_postSEval___closed__1;
x_14 = l_Lean_Meta_Simp_andThen(x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis_go(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_isEq(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isHEq(x_2);
lean_dec(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_expr_has_loose_bvar(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_dec(x_2);
x_1 = x_3;
goto _start;
}
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isFalse(x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis_go(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isForall(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = l_Lean_Meta_Simp_isEqnThmHypothesis_go(x_1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = lean_array_fget(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
x_3 = x_16;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = l_Lean_LocalDecl_isImplementationDetail(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_LocalDecl_type(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_isExprDefEq(x_1, x_22, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_free_object(x_17);
lean_dec(x_20);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_3 = x_16;
x_4 = lean_box(0);
x_12 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = l_Lean_LocalDecl_toExpr(x_20);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_30);
lean_ctor_set(x_23, 0, x_17);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_Lean_LocalDecl_toExpr(x_20);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_17);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_free_object(x_17);
lean_dec(x_20);
x_3 = x_16;
x_4 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
lean_dec(x_17);
x_40 = l_Lean_LocalDecl_isImplementationDetail(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_LocalDecl_type(x_39);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_42 = l_Lean_Meta_isExprDefEq(x_1, x_41, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_39);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_3 = x_16;
x_4 = lean_box(0);
x_12 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = l_Lean_LocalDecl_toExpr(x_39);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_dec(x_39);
x_3 = x_16;
x_4 = lean_box(0);
goto _start;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = lean_array_fget(x_2, x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4(x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_16;
x_4 = lean_box(0);
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_3, x_15);
lean_dec(x_3);
x_17 = lean_array_fget(x_2, x_16);
if (lean_obj_tag(x_17) == 0)
{
x_3 = x_16;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = l_Lean_LocalDecl_isImplementationDetail(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_LocalDecl_type(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_23 = l_Lean_Meta_isExprDefEq(x_1, x_22, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_free_object(x_17);
lean_dec(x_20);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_3 = x_16;
x_4 = lean_box(0);
x_12 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = l_Lean_LocalDecl_toExpr(x_20);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_30);
lean_ctor_set(x_23, 0, x_17);
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = l_Lean_LocalDecl_toExpr(x_20);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_17);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_free_object(x_17);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_23);
if (x_34 == 0)
{
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_free_object(x_17);
lean_dec(x_20);
x_3 = x_16;
x_4 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_17, 0);
lean_inc(x_39);
lean_dec(x_17);
x_40 = l_Lean_LocalDecl_isImplementationDetail(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_Lean_LocalDecl_type(x_39);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_42 = l_Lean_Meta_isExprDefEq(x_1, x_41, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_39);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_3 = x_16;
x_4 = lean_box(0);
x_12 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = l_Lean_LocalDecl_toExpr(x_39);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_39);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_54 = x_42;
} else {
 lean_dec_ref(x_42);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_dec(x_39);
x_3 = x_16;
x_4 = lean_box(0);
goto _start;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_12);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_array_get_size(x_11);
x_13 = l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5(x_1, x_11, x_12, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_array_get_size(x_14);
x_16 = l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6(x_1, x_14, x_15, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3(x_1, x_11, x_12, lean_box(0), x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_25 = x_14;
} else {
 lean_dec_ref(x_14);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeUsingAssumption_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_type(x_9);
lean_dec(x_9);
x_12 = l_Lean_Expr_isEq(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isHEq(x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Meta_unifyEq_x3f(x_2, x_1, x_15, x_17, x_16, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_26, x_3, x_4, x_5, x_6, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = lean_box(0);
x_34 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_35 = l_Lean_Meta_unifyEq_x3f(x_2, x_1, x_32, x_34, x_33, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_43, x_3, x_4, x_5, x_6, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_17; lean_object* x_18; 
x_17 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Meta_intro1Core(x_1, x_17, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2), 7, 2);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_22);
lean_inc(x_4);
x_24 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_22, x_23, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_7 = x_29;
x_8 = x_30;
goto block_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_7 = x_31;
x_8 = x_32;
goto block_16;
}
block_16:
{
uint8_t x_9; 
x_9 = l_Lean_Exception_isRuntime(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_hasMVar(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_st_ref_get(x_3, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_instantiateMVarsCore(x_12, x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_take(x_3, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_15);
x_21 = lean_st_ref_set(x_3, x_17, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_14);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_17, 1);
x_27 = lean_ctor_get(x_17, 2);
x_28 = lean_ctor_get(x_17, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_st_ref_set(x_3, x_29, x_18);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_32 = x_30;
} else {
 lean_dec_ref(x_30);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("assertion violation: ", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("isEqnThmHypothesis e\n  ", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1;
x_2 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Tactic.Simp.Rewrite", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Meta.Simp.dischargeEqnThmHypothesis\?", 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4;
x_2 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5;
x_3 = lean_unsigned_to_nat(451u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_canUnfoldAtMatcher___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6;
x_9 = l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_box(0);
lean_inc(x_2);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_10, x_2, x_3, x_4, x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = l_Lean_Expr_mvarId_x21(x_12);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 5);
lean_dec(x_16);
x_17 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8;
lean_ctor_set(x_2, 5, x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_14, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1(x_12, x_2, x_3, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_18, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_18, 0, x_31);
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_dec(x_18);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_18);
if (x_35 == 0)
{
return x_18;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_ctor_get(x_2, 3);
x_43 = lean_ctor_get(x_2, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_44 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8;
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
lean_ctor_set(x_45, 5, x_44);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_45);
x_46 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(x_14, x_45, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1(x_12, x_45, x_3, x_4, x_5, x_48);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_45);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_50);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_56 = x_46;
} else {
 lean_dec_ref(x_46);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_45);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_61 = x_46;
} else {
 lean_dec_ref(x_46);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maximum discharge depth has been reached", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get_uint32(x_1, sizeof(void*)*4);
x_14 = lean_ctor_get_uint32(x_1, sizeof(void*)*4 + 4);
x_15 = lean_uint32_dec_le(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
uint32_t x_17; uint32_t x_18; uint32_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get_uint32(x_6, sizeof(void*)*4 + 4);
x_18 = 1;
x_19 = lean_uint32_add(x_17, x_18);
lean_ctor_set_uint32(x_6, sizeof(void*)*4 + 4, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = lean_simp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = l_Lean_Expr_isTrue(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_26 = lean_box(0);
lean_ctor_set(x_20, 0, x_26);
return x_20;
}
else
{
lean_object* x_27; 
lean_free_object(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Meta_Simp_Result_getProof(x_22, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_10);
x_30 = l_Lean_Meta_mkOfEqTrue(x_28, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = l_Lean_Exception_isRuntime(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_10);
x_41 = lean_box(0);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_41);
return x_30;
}
else
{
uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; 
lean_dec(x_39);
x_43 = lean_box(0);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = l_Lean_Exception_isRuntime(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_44);
lean_dec(x_10);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_44);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_27);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_27, 0);
x_55 = l_Lean_Exception_isRuntime(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_10);
x_56 = lean_box(0);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_56);
return x_27;
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_57 == 0)
{
return x_27;
}
else
{
lean_object* x_58; 
lean_dec(x_54);
x_58 = lean_box(0);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_58);
return x_27;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_27, 0);
x_60 = lean_ctor_get(x_27, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_27);
x_61 = l_Lean_Exception_isRuntime(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_10);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
uint8_t x_64; 
x_64 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_20, 0);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_20);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = l_Lean_Expr_isTrue(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_68);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
else
{
lean_object* x_74; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_74 = l_Lean_Meta_Simp_Result_getProof(x_68, x_8, x_9, x_10, x_11, x_69);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_10);
x_77 = l_Lean_Meta_mkOfEqTrue(x_75, x_8, x_9, x_10, x_11, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_10);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_78);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_77, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_85 = x_77;
} else {
 lean_dec_ref(x_77);
 x_85 = lean_box(0);
}
x_86 = l_Lean_Exception_isRuntime(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_10);
x_87 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
 lean_ctor_set_tag(x_88, 0);
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_89 == 0)
{
lean_object* x_90; 
if (lean_is_scalar(x_85)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_85;
}
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_84);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_83);
x_91 = lean_box(0);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_85;
 lean_ctor_set_tag(x_92, 0);
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_93 = lean_ctor_get(x_74, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_74, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_95 = x_74;
} else {
 lean_dec_ref(x_74);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Exception_isRuntime(x_93);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
lean_dec(x_10);
x_97 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
 lean_ctor_set_tag(x_98, 0);
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_99 == 0)
{
lean_object* x_100; 
if (lean_is_scalar(x_95)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_95;
}
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_94);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_93);
x_101 = lean_box(0);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_95;
 lean_ctor_set_tag(x_102, 0);
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_94);
return x_102;
}
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_103 = !lean_is_exclusive(x_20);
if (x_103 == 0)
{
return x_20;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_20, 0);
x_105 = lean_ctor_get(x_20, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_20);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; uint32_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint32_t x_112; uint32_t x_113; uint32_t x_114; lean_object* x_115; lean_object* x_116; 
x_107 = lean_ctor_get(x_6, 0);
x_108 = lean_ctor_get_uint32(x_6, sizeof(void*)*4);
x_109 = lean_ctor_get(x_6, 1);
x_110 = lean_ctor_get(x_6, 2);
x_111 = lean_ctor_get(x_6, 3);
x_112 = lean_ctor_get_uint32(x_6, sizeof(void*)*4 + 4);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_107);
lean_dec(x_6);
x_113 = 1;
x_114 = lean_uint32_add(x_112, x_113);
x_115 = lean_alloc_ctor(0, 4, 8);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
lean_ctor_set_uint32(x_115, sizeof(void*)*4, x_108);
lean_ctor_set_uint32(x_115, sizeof(void*)*4 + 4, x_114);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_116 = lean_simp(x_2, x_5, x_115, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
x_121 = l_Lean_Expr_isTrue(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_117);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_122 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_118);
return x_123;
}
else
{
lean_object* x_124; 
lean_dec(x_119);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_124 = l_Lean_Meta_Simp_Result_getProof(x_117, x_8, x_9, x_10, x_11, x_118);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_10);
x_127 = l_Lean_Meta_mkOfEqTrue(x_125, x_8, x_9, x_10, x_11, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_10);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_128);
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_135 = x_127;
} else {
 lean_dec_ref(x_127);
 x_135 = lean_box(0);
}
x_136 = l_Lean_Exception_isRuntime(x_133);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_133);
lean_dec(x_10);
x_137 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_135;
 lean_ctor_set_tag(x_138, 0);
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
return x_138;
}
else
{
uint8_t x_139; 
x_139 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_139 == 0)
{
lean_object* x_140; 
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_133);
x_141 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_135;
 lean_ctor_set_tag(x_142, 0);
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
return x_142;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_143 = lean_ctor_get(x_124, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_124, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_145 = x_124;
} else {
 lean_dec_ref(x_124);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Exception_isRuntime(x_143);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_143);
lean_dec(x_10);
x_147 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_145;
 lean_ctor_set_tag(x_148, 0);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_144);
return x_148;
}
else
{
uint8_t x_149; 
x_149 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_149 == 0)
{
lean_object* x_150; 
if (lean_is_scalar(x_145)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_145;
}
lean_ctor_set(x_150, 0, x_143);
lean_ctor_set(x_150, 1, x_144);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
x_151 = lean_box(0);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_145;
 lean_ctor_set_tag(x_152, 0);
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_153 = lean_ctor_get(x_116, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_116, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_155 = x_116;
} else {
 lean_dec_ref(x_116);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_2);
lean_inc(x_3);
x_157 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_161 = lean_unbox(x_158);
lean_dec(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_3);
x_162 = lean_box(0);
x_163 = lean_apply_9(x_160, x_162, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_159);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2;
x_165 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_3, x_164, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_159);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_apply_9(x_160, x_166, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_167);
return x_168;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_2);
x_11 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
lean_inc(x_4);
x_17 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1(x_4, x_1, x_11, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
lean_inc(x_1);
x_19 = l_Lean_MessageData_ofExpr(x_1);
x_20 = l_Lean_Meta_Simp_dischargeGround___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_11, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_4);
x_27 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1(x_4, x_1, x_11, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_25);
lean_dec(x_4);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_apply_9(x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_24 = x_13;
} else {
 lean_dec_ref(x_13);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(1, 1, 0);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Expr_cleanupAnnotations(x_1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2), 10, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_10);
x_12 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2(x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_15 = l_Lean_Meta_Simp_dischargeUsingAssumption_x3f(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3(x_10, x_11, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_27 = x_16;
} else {
 lean_dec_ref(x_16);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_postDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_preDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkMethods___elambda__2), 10, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkMethods___elambda__1), 10, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeDefault_x3f), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
x_3 = l_Lean_Meta_Simp_mkMethods(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Simp_simprocs;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_2 = l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
x_3 = l_Lean_Meta_Simp_mkMethods(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = l_Lean_Meta_Simp_mkDefaultMethods___closed__1;
x_6 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Simp_mkDefaultMethods___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Meta_Simp_getSimprocs___rarg(x_2, x_3);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
x_15 = l_Lean_Meta_Simp_mkMethods(x_13, x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4;
x_19 = lean_array_push(x_18, x_16);
x_20 = l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
x_21 = l_Lean_Meta_Simp_mkMethods(x_19, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_mkDefaultMethods(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ACLt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatchEqsExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_LinearArith_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ACLt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatchEqsExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_UnifyEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_LinearArith_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3);
l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4 = _init_l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7);
l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8 = _init_l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8();
lean_mark_persistent(l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13);
l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14 = _init_l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4);
l_Lean_Meta_Simp_synthesizeArgs___closed__1 = _init_l_Lean_Meta_Simp_synthesizeArgs___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_synthesizeArgs___closed__1);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6);
l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7 = _init_l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7();
lean_mark_persistent(l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3);
l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4 = _init_l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4();
lean_mark_persistent(l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3);
l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4 = _init_l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6);
l_Lean_Meta_Simp_rewrite_x3f___closed__1 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__1);
l_Lean_Meta_Simp_rewrite_x3f___closed__2 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__2);
l_Lean_Meta_Simp_rewrite_x3f___closed__3 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__3);
l_Lean_Meta_Simp_rewrite_x3f___closed__4 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__4);
l_Lean_Meta_Simp_rewrite_x3f___closed__5 = _init_l_Lean_Meta_Simp_rewrite_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewrite_x3f___closed__5);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___lambda__2___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__1 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__1);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__2 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__2);
l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__3 = _init_l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_reduceOfNatNat___closed__3);
l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__1);
l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__2);
l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__3);
l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___lambda__1___closed__4);
l_Lean_Meta_Simp_simpCtorEq___closed__1 = _init_l_Lean_Meta_Simp_simpCtorEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___closed__1);
l_Lean_Meta_Simp_simpCtorEq___closed__2 = _init_l_Lean_Meta_Simp_simpCtorEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___closed__2);
l_Lean_Meta_Simp_simpCtorEq___closed__3 = _init_l_Lean_Meta_Simp_simpCtorEq___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___closed__3);
l_Lean_Meta_Simp_simpCtorEq___closed__4 = _init_l_Lean_Meta_Simp_simpCtorEq___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___closed__4);
l_Lean_Meta_Simp_simpCtorEq___closed__5 = _init_l_Lean_Meta_Simp_simpCtorEq___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___closed__5);
l_Lean_Meta_Simp_simpCtorEq___closed__6 = _init_l_Lean_Meta_Simp_simpCtorEq___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_simpCtorEq___closed__6);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__1);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__2);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__3);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__4);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__5);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__6);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__7);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__8 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__8);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__9 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__9);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__10);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__11);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__12);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__13 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__13);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__14 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__14);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__15);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__16 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__16);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__17 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__17);
l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18 = _init_l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_simpUsingDecide___lambda__1___closed__18);
l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1);
l_Lean_Meta_Simp_dischargeGround___closed__1 = _init_l_Lean_Meta_Simp_dischargeGround___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeGround___closed__1);
l_Lean_Meta_Simp_dischargeGround___closed__2 = _init_l_Lean_Meta_Simp_dischargeGround___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeGround___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_sevalGround___spec__1___closed__4);
l_Lean_Meta_Simp_sevalGround___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_sevalGround___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_sevalGround___lambda__2___closed__1);
l_Lean_Meta_Simp_sevalGround___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_sevalGround___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_sevalGround___lambda__2___closed__2);
l_Lean_Meta_Simp_preSEval___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_preSEval___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_preSEval___lambda__1___closed__1);
l_Lean_Meta_Simp_preSEval___closed__1 = _init_l_Lean_Meta_Simp_preSEval___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_preSEval___closed__1);
l_Lean_Meta_Simp_postSEval___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_postSEval___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_postSEval___lambda__1___closed__1);
l_Lean_Meta_Simp_postSEval___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_postSEval___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_postSEval___lambda__1___closed__2);
l_Lean_Meta_Simp_postSEval___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_postSEval___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_postSEval___lambda__1___closed__3);
l_Lean_Meta_Simp_postSEval___closed__1 = _init_l_Lean_Meta_Simp_postSEval___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_postSEval___closed__1);
l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1 = _init_l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSEvalMethods___rarg___closed__1);
l_Lean_Meta_Simp_mkSEvalContext___closed__1 = _init_l_Lean_Meta_Simp_mkSEvalContext___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkSEvalContext___closed__1);
l_Lean_Meta_Simp_mkSEvalContext___closed__2 = _init_l_Lean_Meta_Simp_mkSEvalContext___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkSEvalContext___closed__2);
l_Lean_Meta_Simp_mkSEvalContext___closed__3 = _init_l_Lean_Meta_Simp_mkSEvalContext___closed__3();
l_Lean_Meta_Simp_seval___closed__1 = _init_l_Lean_Meta_Simp_seval___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_seval___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__1);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__2 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__2);
l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3 = _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at_Lean_Meta_Simp_simpGround___spec__2___rarg___closed__3);
l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3___closed__1 = _init_l_Lean_withSeconds___at_Lean_Meta_Simp_simpGround___spec__3___closed__1();
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__1);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__2);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__3);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__4 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__4();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__4);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__3___closed__5);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__1);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__4___closed__2);
l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1 = _init_l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1();
lean_mark_persistent(l_Lean_withTraceNode___at_Lean_Meta_Simp_simpGround___spec__1___lambda__5___closed__1);
l_Lean_Meta_Simp_simpGround___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_simpGround___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpGround___lambda__1___closed__1);
l_Lean_Meta_Simp_simpGround___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_simpGround___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_simpGround___lambda__1___closed__2);
l_Lean_Meta_Simp_preDefault___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_preDefault___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_preDefault___lambda__1___closed__1);
l_Lean_Meta_Simp_postDefault___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_postDefault___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_postDefault___lambda__1___closed__1);
l_Lean_Meta_Simp_postDefault___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_postDefault___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_postDefault___lambda__1___closed__2);
l_Lean_Meta_Simp_postDefault___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_postDefault___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_postDefault___lambda__2___closed__1);
l_Lean_Meta_Simp_postDefault___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_postDefault___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_postDefault___lambda__2___closed__2);
l_Lean_Meta_Simp_postDefault___lambda__3___closed__1 = _init_l_Lean_Meta_Simp_postDefault___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_postDefault___lambda__3___closed__1);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7);
l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8 = _init_l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8);
l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2);
l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1 = _init_l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1);
l_Lean_Meta_Simp_mkDefaultMethods___closed__1 = _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethods___closed__1);
l_Lean_Meta_Simp_mkDefaultMethods___closed__2 = _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethods___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
