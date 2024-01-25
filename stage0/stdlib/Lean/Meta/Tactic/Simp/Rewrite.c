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
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__6;
static lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkDefaultMethods___closed__1;
lean_object* l_Lean_Meta_Simp_getDtConfig(lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__9;
lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__6;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeUsingAssumption_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2;
static lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_SimpTheorems_isLemma___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Step_result(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_stripArgsN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4;
lean_object* l_Lean_Expr_getAppArgsN_loop(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__13;
lean_object* l_Lean_Meta_Simp_getSimprocs___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f_inErasedSet___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
extern lean_object* l_Lean_Meta_Simp_simprocs;
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Simp_rewrite_x3f___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__5;
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__5;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis_go(lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3;
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__7;
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_isLevelMVarAssignable___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2;
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__11;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1;
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__2;
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__3;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp___rarg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__7;
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__2;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__5;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_canUnfoldAtMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__3;
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__1;
lean_object* l_Lean_Meta_Linear_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__4;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1;
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_dsimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6;
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Lean_Meta_WHNF_0__Lean_Meta_cached_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l_Lean_Meta_Simp_mkDefaultMethods___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_mkDefaultMethods___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__1;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
static lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Step_updateResult(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_postSimproc_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__1;
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__1;
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4;
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ACLt_main_lt(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__3;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2;
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__3;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__4;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethodsCore(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16;
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__3;
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__7;
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__6___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__6;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_preSimproc_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__8;
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__1;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_isLevelMVarAssignable___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_getConfig___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6;
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__1;
static lean_object* l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__1;
extern lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Instances_erased___default___spec__1;
static lean_object* l_Lean_Meta_Simp_mkDefaultMethods___closed__2;
static lean_object* l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__14;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclRevM_x3f___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_rewrite_x3f___closed__2;
lean_object* l_Lean_Expr_consumeMData(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__3___closed__4;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_Simp_dischargeEqnThmHypothesis_x3f_go_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_Meta_Simp_dischargeUsingAssumption_x3f___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__5;
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
lean_dec(x_12);
lean_ctor_set(x_2, 1, x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = l_Lean_Meta_mkEqTrans(x_18, x_24, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_10, 0, x_27);
lean_ctor_set(x_25, 0, x_2);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_10, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_10);
lean_free_object(x_2);
lean_dec(x_21);
lean_dec(x_20);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_10, 0);
lean_inc(x_35);
lean_dec(x_10);
x_36 = l_Lean_Meta_mkEqTrans(x_18, x_35, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_2, 1, x_40);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_free_object(x_2);
lean_dec(x_21);
lean_dec(x_20);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_2);
x_48 = lean_ctor_get(x_10, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_49 = x_10;
} else {
 lean_dec_ref(x_10);
 x_49 = lean_box(0);
}
x_50 = l_Lean_Meta_mkEqTrans(x_18, x_48, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_51);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_47);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_52);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_46);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_59 = x_50;
} else {
 lean_dec_ref(x_50);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
}
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_dec(x_7);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_16 = l_Lean_Meta_isProp(x_1, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_3);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_st_ref_get(x_10, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 2);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_32 = lean_apply_9(x_4, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_2);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_36 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_1);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_box(0);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_31, x_3, x_40, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_39);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
x_48 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__2;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_indentExpr(x_1);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
x_53 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_35, x_52, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_45);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_31, x_3, x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_55);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_54);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
return x_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_43, 0);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_43);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_dec(x_32);
x_62 = lean_ctor_get(x_33, 0);
lean_inc(x_62);
lean_dec(x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l_Lean_Meta_isExprDefEq(x_6, x_62, x_11, x_12, x_13, x_14, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___closed__5;
x_68 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_67, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_1);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_box(0);
x_73 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_31, x_3, x_72, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_71);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
lean_dec(x_68);
x_75 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
x_80 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2___closed__4;
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_indentExpr(x_1);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_78);
x_85 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_67, x_84, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_77);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1(x_31, x_3, x_86, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_87);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_86);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_75);
if (x_89 == 0)
{
return x_75;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_75, 0);
x_91 = lean_ctor_get(x_75, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_75);
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
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_63);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_63, 0);
lean_dec(x_94);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_2);
lean_ctor_set(x_95, 1, x_3);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_63, 0, x_96);
return x_63;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_63, 1);
lean_inc(x_97);
lean_dec(x_63);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_2);
lean_ctor_set(x_98, 1, x_3);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_97);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_63);
if (x_101 == 0)
{
return x_63;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_63, 0);
x_103 = lean_ctor_get(x_63, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_63);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_31);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_32);
if (x_105 == 0)
{
return x_32;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_32, 0);
x_107 = lean_ctor_get(x_32, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_32);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_16);
if (x_109 == 0)
{
return x_16;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_16, 0);
x_111 = lean_ctor_get(x_16, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_16);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_28; 
x_18 = lean_array_uget(x_4, x_6);
x_28 = !lean_is_exclusive(x_7);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_7, 1);
x_30 = lean_ctor_get(x_7, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
x_34 = lean_nat_dec_lt(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_18);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_7);
x_19 = x_35;
x_20 = x_15;
goto block_27;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_29, 2);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_array_fget(x_31, x_32);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_32, x_42);
lean_dec(x_32);
lean_ctor_set(x_29, 1, x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_44 = lean_infer_type(x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_BinderInfo_isInstImplicit(x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_inc(x_18);
x_48 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Expr_isMVar(x_49);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_18);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_7);
x_19 = x_52;
x_20 = x_50;
goto block_27;
}
else
{
lean_object* x_53; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_45);
x_53 = l_Lean_Meta_isClass_x3f(x_45, x_11, x_12, x_13, x_14, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_7);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_57 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_45, x_3, x_29, x_2, x_1, x_18, x_56, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_19 = x_58;
x_20 = x_59;
goto block_27;
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 0);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_57);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_54);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_dec(x_53);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_45);
lean_inc(x_18);
lean_inc(x_1);
x_65 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_18, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_free_object(x_7);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_70 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_45, x_3, x_29, x_2, x_1, x_18, x_69, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_19 = x_71;
x_20 = x_72;
goto block_27;
}
else
{
uint8_t x_73; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_45);
lean_dec(x_18);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_dec(x_65);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_7);
x_19 = x_78;
x_20 = x_77;
goto block_27;
}
}
else
{
uint8_t x_79; 
lean_dec(x_45);
lean_dec(x_29);
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_65);
if (x_79 == 0)
{
return x_65;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_65, 0);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_65);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_45);
lean_dec(x_29);
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_53);
if (x_83 == 0)
{
return x_53;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_53, 0);
x_85 = lean_ctor_get(x_53, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_53);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_87 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_18, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_7, 0, x_91);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_7);
x_19 = x_92;
x_20 = x_90;
goto block_27;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
lean_inc(x_3);
lean_ctor_set(x_7, 0, x_3);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_7);
x_19 = x_94;
x_20 = x_93;
goto block_27;
}
}
else
{
uint8_t x_95; 
lean_dec(x_29);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_87);
if (x_95 == 0)
{
return x_87;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_87, 0);
x_97 = lean_ctor_get(x_87, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_87);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_29);
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
return x_44;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_44, 0);
x_101 = lean_ctor_get(x_44, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_44);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_29);
x_103 = lean_array_fget(x_31, x_32);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_add(x_32, x_105);
lean_dec(x_32);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_31);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_33);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_108 = lean_infer_type(x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_BinderInfo_isInstImplicit(x_104);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_inc(x_18);
x_112 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_110);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_isMVar(x_113);
lean_dec(x_113);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_109);
lean_dec(x_18);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_107);
lean_ctor_set(x_7, 0, x_3);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_7);
x_19 = x_116;
x_20 = x_114;
goto block_27;
}
else
{
lean_object* x_117; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_109);
x_117 = l_Lean_Meta_isClass_x3f(x_109, x_11, x_12, x_13, x_14, x_114);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_free_object(x_7);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_121 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_109, x_3, x_107, x_2, x_1, x_18, x_120, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_119);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_19 = x_122;
x_20 = x_123;
goto block_27;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_126 = x_121;
} else {
 lean_dec_ref(x_121);
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
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_118);
x_128 = lean_ctor_get(x_117, 1);
lean_inc(x_128);
lean_dec(x_117);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_109);
lean_inc(x_18);
lean_inc(x_1);
x_129 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_18, x_109, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_7);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_134 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_109, x_3, x_107, x_2, x_1, x_18, x_133, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_19 = x_135;
x_20 = x_136;
goto block_27;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_139 = x_134;
} else {
 lean_dec_ref(x_134);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_109);
lean_dec(x_18);
x_141 = lean_ctor_get(x_129, 1);
lean_inc(x_141);
lean_dec(x_129);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_107);
lean_ctor_set(x_7, 0, x_3);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_7);
x_19 = x_142;
x_20 = x_141;
goto block_27;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_109);
lean_dec(x_107);
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_129, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_129, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_145 = x_129;
} else {
 lean_dec_ref(x_129);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_109);
lean_dec(x_107);
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_ctor_get(x_117, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_117, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_149 = x_117;
} else {
 lean_dec_ref(x_117);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
else
{
lean_object* x_151; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_151 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_18, x_109, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_110);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
lean_ctor_set(x_7, 1, x_107);
lean_ctor_set(x_7, 0, x_155);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_7);
x_19 = x_156;
x_20 = x_154;
goto block_27;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
lean_dec(x_151);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_107);
lean_ctor_set(x_7, 0, x_3);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_7);
x_19 = x_158;
x_20 = x_157;
goto block_27;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_107);
lean_free_object(x_7);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_161 = x_151;
} else {
 lean_dec_ref(x_151);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_107);
lean_free_object(x_7);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = lean_ctor_get(x_108, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_108, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_165 = x_108;
} else {
 lean_dec_ref(x_108);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_7, 1);
lean_inc(x_167);
lean_dec(x_7);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 2);
lean_inc(x_170);
x_171 = lean_nat_dec_lt(x_169, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_18);
lean_inc(x_3);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_3);
lean_ctor_set(x_172, 1, x_167);
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
x_19 = x_173;
x_20 = x_15;
goto block_27;
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 lean_ctor_release(x_167, 2);
 x_174 = x_167;
} else {
 lean_dec_ref(x_167);
 x_174 = lean_box(0);
}
x_175 = lean_array_fget(x_168, x_169);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_add(x_169, x_177);
lean_dec(x_169);
if (lean_is_scalar(x_174)) {
 x_179 = lean_alloc_ctor(0, 3, 0);
} else {
 x_179 = x_174;
}
lean_ctor_set(x_179, 0, x_168);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_170);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_18);
x_180 = lean_infer_type(x_18, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_BinderInfo_isInstImplicit(x_176);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
lean_inc(x_18);
x_184 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_182);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Expr_isMVar(x_185);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_181);
lean_dec(x_18);
lean_inc(x_3);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_3);
lean_ctor_set(x_188, 1, x_179);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_19 = x_189;
x_20 = x_186;
goto block_27;
}
else
{
lean_object* x_190; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_181);
x_190 = l_Lean_Meta_isClass_x3f(x_181, x_11, x_12, x_13, x_14, x_186);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_194 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_181, x_3, x_179, x_2, x_1, x_18, x_193, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_192);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_19 = x_195;
x_20 = x_196;
goto block_27;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_194, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_194, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_199 = x_194;
} else {
 lean_dec_ref(x_194);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_191);
x_201 = lean_ctor_get(x_190, 1);
lean_inc(x_201);
lean_dec(x_190);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_181);
lean_inc(x_18);
lean_inc(x_1);
x_202 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_18, x_181, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_unbox(x_203);
lean_dec(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
lean_dec(x_202);
x_206 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_2);
lean_inc(x_3);
x_207 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__2(x_181, x_3, x_179, x_2, x_1, x_18, x_206, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_205);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_19 = x_208;
x_20 = x_209;
goto block_27;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_207, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_212 = x_207;
} else {
 lean_dec_ref(x_207);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_181);
lean_dec(x_18);
x_214 = lean_ctor_get(x_202, 1);
lean_inc(x_214);
lean_dec(x_202);
lean_inc(x_3);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_3);
lean_ctor_set(x_215, 1, x_179);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_19 = x_216;
x_20 = x_214;
goto block_27;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_202, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_202, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_219 = x_202;
} else {
 lean_dec_ref(x_202);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = lean_ctor_get(x_190, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_190, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_223 = x_190;
} else {
 lean_dec_ref(x_190);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
}
}
else
{
lean_object* x_225; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_225 = l_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance(x_1, x_18, x_181, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_182);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_unbox(x_226);
lean_dec(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_225, 1);
lean_inc(x_228);
lean_dec(x_225);
x_229 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___lambda__1___closed__1;
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_179);
x_231 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_231, 0, x_230);
x_19 = x_231;
x_20 = x_228;
goto block_27;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_225, 1);
lean_inc(x_232);
lean_dec(x_225);
lean_inc(x_3);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_3);
lean_ctor_set(x_233, 1, x_179);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
x_19 = x_234;
x_20 = x_232;
goto block_27;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_179);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_ctor_get(x_225, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_225, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_237 = x_225;
} else {
 lean_dec_ref(x_225);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_179);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = lean_ctor_get(x_180, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_180, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_241 = x_180;
} else {
 lean_dec_ref(x_180);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_6, x_24);
x_6 = x_25;
x_7 = x_23;
x_15 = x_20;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_13 = lean_array_get_size(x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_toSubarray___rarg(x_3, x_14, x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_array_get_size(x_2);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(x_1, x_4, x_16, x_2, x_19, x_20, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Lean_Meta_Simp_synthesizeArgs___closed__1;
x_26 = lean_box(0);
x_27 = lean_apply_9(x_25, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
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
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_synthesizeArgs___spec__2(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_synthesizeArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_synthesizeArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
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
x_3 = lean_unsigned_to_nat(400u);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_1);
x_17 = l_Lean_Meta_isExprDefEq(x_1, x_8, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_22 = l_Lean_Expr_isMVar(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__2;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_apply_9(x_21, x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
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
x_36 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__4;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_indentExpr(x_1);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___closed__6;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_indentExpr(x_8);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
x_45 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_23, x_44, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_33);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_apply_9(x_21, x_46, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_47);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
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
lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_apply_9(x_21, x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_20);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_dec(x_17);
x_56 = lean_ctor_get(x_6, 4);
lean_inc(x_56);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_56);
x_57 = l_Lean_Meta_Simp_synthesizeArgs(x_56, x_2, x_3, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_57);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_57, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_57, 0, x_62);
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_dec(x_57);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_box(0);
x_68 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__7(x_5, x_56, x_6, x_8, x_4, x_2, x_67, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_56);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_57);
if (x_69 == 0)
{
return x_57;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_57, 0);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_57);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_15);
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
x_73 = !lean_is_exclusive(x_17);
if (x_73 == 0)
{
return x_17;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_17, 0);
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_17);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_22 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_SimprocEntry_try_x3f___spec__1(x_8, x_20, x_8, x_21, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Array_reverse___rarg(x_26);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_28 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go(x_1, x_2, x_3, x_4, x_5, x_7, x_9, x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_39 = l_Lean_hasAssignableMVar___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__2(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_7);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___lambda__1(x_37, x_27, x_43, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_42);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_37);
lean_dec(x_27);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__3___closed__2;
x_47 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_46, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_47, 0, x_52);
return x_47;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_dec(x_47);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = l_Lean_Meta_ppSimpTheorem___at___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___spec__1(x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
x_62 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__3;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_46, x_63, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_59);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_57);
if (x_71 == 0)
{
return x_57;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_57, 0);
x_73 = lean_ctor_get(x_57, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_57);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_37);
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_75 = !lean_is_exclusive(x_39);
if (x_75 == 0)
{
return x_39;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_39, 0);
x_77 = lean_ctor_get(x_39, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_39);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_27);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
x_79 = !lean_is_exclusive(x_28);
if (x_79 == 0)
{
return x_28;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_28, 0);
x_81 = lean_ctor_get(x_28, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_28);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_14 = lean_infer_type(x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = 1;
x_19 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallMetaTelescopeReducingAux(x_15, x_18, x_17, x_19, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_instantiateMVars___at_Lean_Meta_Simp_synthesizeArgs___spec__1(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_23);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = lean_whnf(x_28, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_appFn_x21(x_31);
x_34 = l_Lean_Expr_appArg_x21(x_33);
lean_dec(x_33);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_34, x_24, x_25, x_5, x_31, x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_25);
lean_dec(x_24);
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
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
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
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
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
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_inc(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_13, 0, x_2);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__2), 13, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__1___rarg), 10, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = 0;
x_17 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___spec__2___rarg(x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_appFn_x21(x_30);
x_33 = l_Lean_Expr_appArg_x21(x_32);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_30);
lean_inc(x_4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_33);
x_35 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_33, x_23, x_24, x_4, x_30, x_1, x_2, x_34, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_31);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_33, x_34);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_34);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_33);
lean_dec(x_30);
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
lean_ctor_set(x_35, 0, x_16);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_35);
x_43 = lean_nat_sub(x_41, x_40);
lean_dec(x_40);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_33, x_23, x_24, x_4, x_30, x_1, x_2, x_43, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_33, x_34);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_34);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_33);
lean_dec(x_30);
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
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_16);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_nat_sub(x_47, x_46);
lean_dec(x_46);
lean_dec(x_47);
x_51 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore(x_33, x_23, x_24, x_4, x_30, x_1, x_2, x_50, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_33);
lean_dec(x_30);
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
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_35, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_36, 0);
lean_inc(x_55);
lean_dec(x_36);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_35, 0, x_56);
return x_35;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_ctor_get(x_35, 1);
lean_inc(x_57);
lean_dec(x_35);
x_58 = lean_ctor_get(x_36, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_59 = x_36;
} else {
 lean_dec_ref(x_36);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 1, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_33);
lean_dec(x_30);
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
x_62 = !lean_is_exclusive(x_35);
if (x_62 == 0)
{
return x_35;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_35, 0);
x_64 = lean_ctor_get(x_35, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_35);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
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
x_66 = !lean_is_exclusive(x_29);
if (x_66 == 0)
{
return x_29;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_29, 0);
x_68 = lean_ctor_get(x_29, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_29);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
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
x_70 = !lean_is_exclusive(x_19);
if (x_70 == 0)
{
return x_19;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_19, 0);
x_72 = lean_ctor_get(x_19, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_19);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
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
x_74 = !lean_is_exclusive(x_13);
if (x_74 == 0)
{
return x_13;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_13, 0);
x_76 = lean_ctor_get(x_13, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_13);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f___lambda__1___boxed), 9, 1);
lean_closure_set(x_12, 0, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_tryTheorem_x3f___lambda__1), 12, 3);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_8, x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_70; 
lean_dec(x_9);
x_20 = lean_array_uget(x_6, x_8);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
lean_inc(x_30);
lean_inc(x_2);
x_70 = l_Lean_Meta_Simp_rewrite_x3f_inErasedSet(x_2, x_30);
if (x_70 == 0)
{
if (x_4 == 0)
{
lean_object* x_71; 
x_71 = lean_box(0);
x_32 = x_71;
goto block_69;
}
else
{
uint8_t x_72; 
x_72 = lean_ctor_get_uint8(x_30, sizeof(void*)*5 + 2);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_31);
lean_dec(x_30);
lean_inc(x_5);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_5);
x_21 = x_73;
x_22 = x_17;
goto block_29;
}
else
{
lean_object* x_74; 
x_74 = lean_box(0);
x_32 = x_74;
goto block_69;
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_31);
lean_dec(x_30);
lean_inc(x_5);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_5);
x_21 = x_75;
x_22 = x_17;
goto block_29;
}
block_29:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = 1;
x_27 = lean_usize_add(x_8, x_26);
x_8 = x_27;
x_9 = x_25;
x_17 = x_22;
goto _start;
}
}
block_69:
{
lean_object* x_33; 
lean_dec(x_32);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_1);
x_33 = l_Lean_Meta_Simp_tryTheoremWithExtraArgs_x3f(x_1, x_30, x_31, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_5);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_21 = x_36;
x_22 = x_35;
goto block_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
lean_dec(x_34);
x_39 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
x_40 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_39, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_38, x_44, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_21 = x_46;
x_22 = x_47;
goto block_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
lean_inc(x_1);
x_49 = l_Lean_MessageData_ofExpr(x_1);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__4;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__6;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_ctor_get(x_38, 0);
lean_inc(x_54);
x_55 = l_Lean_MessageData_ofExpr(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_39, x_58, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_48);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___lambda__1(x_38, x_60, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_61);
lean_dec(x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_21 = x_63;
x_22 = x_64;
goto block_29;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_Meta_Simp_getConfig___rarg(x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Simp_getDtConfig(x_16);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_1);
x_19 = l_Lean_Meta_DiscrTree_getMatchWithExtra___rarg(x_2, x_1, x_18, x_10, x_11, x_12, x_13, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_isEmpty___rarg(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_array_get_size(x_20);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_insertionSort_traverse___at_Lean_Meta_Simp_rewrite_x3f___spec__1(x_20, x_24, x_23);
x_26 = lean_box(0);
x_27 = lean_array_get_size(x_25);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
x_31 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(x_1, x_3, x_4, x_6, x_30, x_25, x_28, x_29, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
lean_dec(x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
lean_ctor_set(x_31, 0, x_26);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_26);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_31, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_40);
return x_31;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_dec(x_31);
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
x_48 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___closed__2;
x_49 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_21);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_53 = lean_unbox(x_50);
lean_dec(x_50);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_apply_9(x_52, x_54, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = l_Lean_stringToMessageData(x_5);
x_57 = l_Lean_Meta_Simp_rewrite_x3f___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_Simp_rewrite_x3f___closed__5;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_ofExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_ppOrigin___at_Lean_Meta_Simp_synthesizeArgs_synthesizeInstance___spec__1___closed__4;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_48, x_64, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_51);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_apply_9(x_52, x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_19);
if (x_69 == 0)
{
return x_19;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_19, 0);
x_71 = lean_ctor_get(x_19, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_19);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewrite_x3f___spec__3(x_1, x_2, x_3, x_18, x_5, x_6, x_19, x_20, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_21;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewrite_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Simp_Step_result(x_14);
x_17 = l_Lean_Meta_Simp_mkEqTrans(x_11, x_16, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Meta_Simp_Step_updateResult(x_14, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = l_Lean_Meta_Simp_Step_updateResult(x_14, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_andThen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_9(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Meta_Simp_Step_result(x_20);
x_22 = l_Lean_Meta_Simp_mkEqTrans(x_11, x_21, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = l_Lean_Meta_Simp_Step_updateResult(x_20, x_24);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = l_Lean_Meta_Simp_Step_updateResult(x_20, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_20);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkNoConfusion(x_7, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4;
x_12 = lean_array_push(x_11, x_1);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkLambdaFVars(x_12, x_9, x_13, x_14, x_15, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkEqFalse_x27(x_17, x_2, x_3, x_4, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_8);
if (x_41 == 0)
{
return x_8;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_8, 0);
x_43 = lean_ctor_get(x_8, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_8);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Eq", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteCtorEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_Expr_appFn_x21(x_1);
x_13 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_14 = l_Lean_Expr_appArg_x21(x_1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 3;
lean_ctor_set_uint8(x_16, 9, x_18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = lean_whnf(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = lean_whnf(x_14, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_5, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 0;
lean_inc(x_29);
x_31 = l_Lean_Expr_constructorApp_x3f(x_29, x_20, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_25, 0, x_32);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_constructorApp_x3f(x_29, x_23, x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_name_eq(x_40, x_42);
lean_dec(x_42);
lean_dec(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_free_object(x_25);
x_44 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_45 = 0;
x_46 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_47 = 0;
x_48 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_44, x_45, x_1, x_46, x_47, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_25, 0, x_57);
return x_25;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = 0;
lean_inc(x_60);
x_62 = l_Lean_Expr_constructorApp_x3f(x_60, x_20, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
x_66 = l_Lean_Expr_constructorApp_x3f(x_60, x_23, x_61);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_name_eq(x_73, x_75);
lean_dec(x_75);
lean_dec(x_73);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_77 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_78 = 0;
x_79 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_80 = 0;
x_81 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_77, x_78, x_1, x_79, x_80, x_2, x_3, x_4, x_5, x_59);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_59);
return x_91;
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_22);
if (x_92 == 0)
{
return x_22;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_22, 0);
x_94 = lean_ctor_get(x_22, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_22);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_19);
if (x_96 == 0)
{
return x_19;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_19, 0);
x_98 = lean_ctor_get(x_19, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_19);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get_uint8(x_16, 0);
x_101 = lean_ctor_get_uint8(x_16, 1);
x_102 = lean_ctor_get_uint8(x_16, 2);
x_103 = lean_ctor_get_uint8(x_16, 3);
x_104 = lean_ctor_get_uint8(x_16, 4);
x_105 = lean_ctor_get_uint8(x_16, 5);
x_106 = lean_ctor_get_uint8(x_16, 6);
x_107 = lean_ctor_get_uint8(x_16, 7);
x_108 = lean_ctor_get_uint8(x_16, 8);
x_109 = lean_ctor_get_uint8(x_16, 10);
x_110 = lean_ctor_get_uint8(x_16, 11);
lean_dec(x_16);
x_111 = 3;
x_112 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_112, 0, x_100);
lean_ctor_set_uint8(x_112, 1, x_101);
lean_ctor_set_uint8(x_112, 2, x_102);
lean_ctor_set_uint8(x_112, 3, x_103);
lean_ctor_set_uint8(x_112, 4, x_104);
lean_ctor_set_uint8(x_112, 5, x_105);
lean_ctor_set_uint8(x_112, 6, x_106);
lean_ctor_set_uint8(x_112, 7, x_107);
lean_ctor_set_uint8(x_112, 8, x_108);
lean_ctor_set_uint8(x_112, 9, x_111);
lean_ctor_set_uint8(x_112, 10, x_109);
lean_ctor_set_uint8(x_112, 11, x_110);
lean_ctor_set(x_2, 0, x_112);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_113 = lean_whnf(x_13, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_116 = lean_whnf(x_14, x_2, x_3, x_4, x_5, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_st_ref_get(x_5, x_118);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
lean_dec(x_120);
x_124 = 0;
lean_inc(x_123);
x_125 = l_Lean_Expr_constructorApp_x3f(x_123, x_114, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_123);
lean_dec(x_117);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_122;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_121);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l_Lean_Expr_constructorApp_x3f(x_123, x_117, x_124);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_130 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_122;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_121);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
lean_dec(x_128);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_name_eq(x_136, x_138);
lean_dec(x_138);
lean_dec(x_136);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
lean_dec(x_122);
x_140 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_141 = 0;
x_142 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_143 = 0;
x_144 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_140, x_141, x_1, x_142, x_143, x_2, x_3, x_4, x_5, x_121);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_144, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_151 = x_144;
} else {
 lean_dec_ref(x_144);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_box(0);
if (lean_is_scalar(x_122)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_122;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_121);
return x_154;
}
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_114);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_155 = lean_ctor_get(x_116, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_116, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_157 = x_116;
} else {
 lean_dec_ref(x_116);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_2);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = lean_ctor_get(x_113, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_113, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_161 = x_113;
} else {
 lean_dec_ref(x_113);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_163 = lean_ctor_get(x_2, 0);
x_164 = lean_ctor_get(x_2, 1);
x_165 = lean_ctor_get(x_2, 2);
x_166 = lean_ctor_get(x_2, 3);
x_167 = lean_ctor_get(x_2, 4);
x_168 = lean_ctor_get(x_2, 5);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_2);
x_169 = lean_ctor_get_uint8(x_163, 0);
x_170 = lean_ctor_get_uint8(x_163, 1);
x_171 = lean_ctor_get_uint8(x_163, 2);
x_172 = lean_ctor_get_uint8(x_163, 3);
x_173 = lean_ctor_get_uint8(x_163, 4);
x_174 = lean_ctor_get_uint8(x_163, 5);
x_175 = lean_ctor_get_uint8(x_163, 6);
x_176 = lean_ctor_get_uint8(x_163, 7);
x_177 = lean_ctor_get_uint8(x_163, 8);
x_178 = lean_ctor_get_uint8(x_163, 10);
x_179 = lean_ctor_get_uint8(x_163, 11);
if (lean_is_exclusive(x_163)) {
 x_180 = x_163;
} else {
 lean_dec_ref(x_163);
 x_180 = lean_box(0);
}
x_181 = 3;
if (lean_is_scalar(x_180)) {
 x_182 = lean_alloc_ctor(0, 0, 12);
} else {
 x_182 = x_180;
}
lean_ctor_set_uint8(x_182, 0, x_169);
lean_ctor_set_uint8(x_182, 1, x_170);
lean_ctor_set_uint8(x_182, 2, x_171);
lean_ctor_set_uint8(x_182, 3, x_172);
lean_ctor_set_uint8(x_182, 4, x_173);
lean_ctor_set_uint8(x_182, 5, x_174);
lean_ctor_set_uint8(x_182, 6, x_175);
lean_ctor_set_uint8(x_182, 7, x_176);
lean_ctor_set_uint8(x_182, 8, x_177);
lean_ctor_set_uint8(x_182, 9, x_181);
lean_ctor_set_uint8(x_182, 10, x_178);
lean_ctor_set_uint8(x_182, 11, x_179);
x_183 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_164);
lean_ctor_set(x_183, 2, x_165);
lean_ctor_set(x_183, 3, x_166);
lean_ctor_set(x_183, 4, x_167);
lean_ctor_set(x_183, 5, x_168);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_183);
x_184 = lean_whnf(x_13, x_183, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_183);
x_187 = lean_whnf(x_14, x_183, x_3, x_4, x_5, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_st_ref_get(x_5, x_189);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
x_194 = lean_ctor_get(x_191, 0);
lean_inc(x_194);
lean_dec(x_191);
x_195 = 0;
lean_inc(x_194);
x_196 = l_Lean_Expr_constructorApp_x3f(x_194, x_185, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_194);
lean_dec(x_188);
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_197 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_193;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_192);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
lean_dec(x_196);
x_200 = l_Lean_Expr_constructorApp_x3f(x_194, x_188, x_195);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec(x_199);
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_201 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_193;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_192);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_203 = lean_ctor_get(x_200, 0);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_ctor_get(x_199, 0);
lean_inc(x_204);
lean_dec(x_199);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_dec(x_206);
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
lean_dec(x_205);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_name_eq(x_207, x_209);
lean_dec(x_209);
lean_dec(x_207);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
lean_dec(x_193);
x_211 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4;
x_212 = 0;
x_213 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5;
x_214 = 0;
x_215 = l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_removeUnusedArguments_x3f___spec__2___rarg(x_211, x_212, x_1, x_213, x_214, x_183, x_3, x_4, x_5, x_192);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_215, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_222 = x_215;
} else {
 lean_dec_ref(x_215);
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
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_224 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_193;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_192);
return x_225;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_226 = lean_ctor_get(x_187, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_187, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_228 = x_187;
} else {
 lean_dec_ref(x_187);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_183);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_230 = lean_ctor_get(x_184, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_184, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_232 = x_184;
} else {
 lean_dec_ref(x_184);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_rewriteCtorEq_x3f(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
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
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_11, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_28 = x_11;
} else {
 lean_dec_ref(x_11);
 x_28 = lean_box(0);
}
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_27);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(1, 1, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteCtorEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_tryRewriteCtorEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3;
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false_of_decide", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true_of_decide", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewriteUsingDecide_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Expr_hasFVar(x_1);
if (x_7 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_hasMVar(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_consumeMData(x_1);
x_20 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
x_23 = l_Lean_Expr_isConstOf(x_19, x_22);
lean_dec(x_19);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
x_30 = lean_ctor_get(x_2, 4);
x_31 = lean_ctor_get(x_2, 5);
x_32 = lean_ctor_get_uint8(x_25, 0);
x_33 = lean_ctor_get_uint8(x_25, 1);
x_34 = lean_ctor_get_uint8(x_25, 2);
x_35 = lean_ctor_get_uint8(x_25, 3);
x_36 = lean_ctor_get_uint8(x_25, 4);
x_37 = lean_ctor_get_uint8(x_25, 5);
x_38 = lean_ctor_get_uint8(x_25, 6);
x_39 = lean_ctor_get_uint8(x_25, 7);
x_40 = lean_ctor_get_uint8(x_25, 8);
x_41 = lean_ctor_get_uint8(x_25, 10);
x_42 = lean_ctor_get_uint8(x_25, 11);
x_43 = 3;
lean_ctor_set_uint8(x_25, 9, x_43);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_48, 0, x_32);
lean_ctor_set_uint8(x_48, 1, x_33);
lean_ctor_set_uint8(x_48, 2, x_34);
lean_ctor_set_uint8(x_48, 3, x_35);
lean_ctor_set_uint8(x_48, 4, x_36);
lean_ctor_set_uint8(x_48, 5, x_37);
lean_ctor_set_uint8(x_48, 6, x_38);
lean_ctor_set_uint8(x_48, 7, x_39);
lean_ctor_set_uint8(x_48, 8, x_40);
lean_ctor_set_uint8(x_48, 9, x_47);
lean_ctor_set_uint8(x_48, 10, x_41);
lean_ctor_set_uint8(x_48, 11, x_42);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_27);
lean_ctor_set(x_49, 2, x_28);
lean_ctor_set(x_49, 3, x_29);
lean_ctor_set(x_49, 4, x_30);
lean_ctor_set(x_49, 5, x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_45);
x_50 = lean_whnf(x_45, x_49, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_55 = l_Lean_Expr_isConstOf(x_52, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_57 = l_Lean_Expr_isConstOf(x_52, x_56);
lean_dec(x_52);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_50, 0, x_58);
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_50);
x_59 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
lean_inc(x_4);
x_60 = l_Lean_Meta_mkEqRefl(x_59, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_64 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_65 = lean_array_push(x_64, x_1);
x_66 = lean_array_push(x_65, x_63);
x_67 = lean_array_push(x_66, x_62);
x_68 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_69 = l_Lean_mkAppN(x_68, x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_60, 0, x_74);
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_78 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_79 = lean_array_push(x_78, x_1);
x_80 = lean_array_push(x_79, x_77);
x_81 = lean_array_push(x_80, x_75);
x_82 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_83 = l_Lean_mkAppN(x_82, x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_84);
lean_ctor_set(x_87, 2, x_86);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_76);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_45);
lean_dec(x_1);
x_90 = lean_ctor_get(x_60, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_60, 1);
lean_inc(x_91);
lean_dec(x_60);
x_8 = x_90;
x_9 = x_91;
goto block_17;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_free_object(x_50);
lean_dec(x_52);
x_92 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
lean_inc(x_4);
x_93 = l_Lean_Meta_mkEqRefl(x_92, x_2, x_3, x_4, x_5, x_53);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_97 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_array_push(x_98, x_96);
x_100 = lean_array_push(x_99, x_95);
x_101 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_102 = l_Lean_mkAppN(x_101, x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_105 = lean_unsigned_to_nat(0u);
x_106 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_103);
lean_ctor_set(x_106, 2, x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_93, 0, x_107);
return x_93;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_108 = lean_ctor_get(x_93, 0);
x_109 = lean_ctor_get(x_93, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_93);
x_110 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_111 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_112 = lean_array_push(x_111, x_1);
x_113 = lean_array_push(x_112, x_110);
x_114 = lean_array_push(x_113, x_108);
x_115 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_116 = l_Lean_mkAppN(x_115, x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_117);
lean_ctor_set(x_120, 2, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_109);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_45);
lean_dec(x_1);
x_123 = lean_ctor_get(x_93, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_93, 1);
lean_inc(x_124);
lean_dec(x_93);
x_8 = x_123;
x_9 = x_124;
goto block_17;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_125 = lean_ctor_get(x_50, 0);
x_126 = lean_ctor_get(x_50, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_50);
x_127 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_128 = l_Lean_Expr_isConstOf(x_125, x_127);
if (x_128 == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_130 = l_Lean_Expr_isConstOf(x_125, x_129);
lean_dec(x_125);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_131 = lean_box(0);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_126);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
lean_inc(x_4);
x_134 = l_Lean_Meta_mkEqRefl(x_133, x_2, x_3, x_4, x_5, x_126);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_4);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_138 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_139 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_140 = lean_array_push(x_139, x_1);
x_141 = lean_array_push(x_140, x_138);
x_142 = lean_array_push(x_141, x_135);
x_143 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_144 = l_Lean_mkAppN(x_143, x_142);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_145);
lean_ctor_set(x_148, 2, x_147);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
if (lean_is_scalar(x_137)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_137;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_136);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_45);
lean_dec(x_1);
x_151 = lean_ctor_get(x_134, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_134, 1);
lean_inc(x_152);
lean_dec(x_134);
x_8 = x_151;
x_9 = x_152;
goto block_17;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_125);
x_153 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
lean_inc(x_4);
x_154 = l_Lean_Meta_mkEqRefl(x_153, x_2, x_3, x_4, x_5, x_126);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_4);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = l_Lean_Expr_appArg_x21(x_45);
lean_dec(x_45);
x_159 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_160 = lean_array_push(x_159, x_1);
x_161 = lean_array_push(x_160, x_158);
x_162 = lean_array_push(x_161, x_155);
x_163 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_164 = l_Lean_mkAppN(x_163, x_162);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_165);
lean_ctor_set(x_168, 2, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
if (lean_is_scalar(x_157)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_157;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_156);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_45);
lean_dec(x_1);
x_171 = lean_ctor_get(x_154, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_154, 1);
lean_inc(x_172);
lean_dec(x_154);
x_8 = x_171;
x_9 = x_172;
goto block_17;
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_45);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_ctor_get(x_50, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_50, 1);
lean_inc(x_174);
lean_dec(x_50);
x_8 = x_173;
x_9 = x_174;
goto block_17;
}
}
else
{
uint8_t x_175; 
lean_dec(x_2);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_44);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_44, 0);
x_177 = l_Lean_Exception_isRuntime(x_176);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_176);
lean_dec(x_4);
x_178 = lean_box(0);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_178);
return x_44;
}
else
{
uint8_t x_179; 
x_179 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_179 == 0)
{
return x_44;
}
else
{
lean_object* x_180; 
lean_dec(x_176);
x_180 = lean_box(0);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_180);
return x_44;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_44, 0);
x_182 = lean_ctor_get(x_44, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_44);
x_183 = l_Lean_Exception_isRuntime(x_181);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_181);
lean_dec(x_4);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
else
{
uint8_t x_186; 
x_186 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_186 == 0)
{
lean_object* x_187; 
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_182);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_181);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_182);
return x_189;
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
x_190 = lean_ctor_get(x_2, 1);
x_191 = lean_ctor_get(x_2, 2);
x_192 = lean_ctor_get(x_2, 3);
x_193 = lean_ctor_get(x_2, 4);
x_194 = lean_ctor_get(x_2, 5);
x_195 = lean_ctor_get_uint8(x_25, 0);
x_196 = lean_ctor_get_uint8(x_25, 1);
x_197 = lean_ctor_get_uint8(x_25, 2);
x_198 = lean_ctor_get_uint8(x_25, 3);
x_199 = lean_ctor_get_uint8(x_25, 4);
x_200 = lean_ctor_get_uint8(x_25, 5);
x_201 = lean_ctor_get_uint8(x_25, 6);
x_202 = lean_ctor_get_uint8(x_25, 7);
x_203 = lean_ctor_get_uint8(x_25, 8);
x_204 = lean_ctor_get_uint8(x_25, 10);
x_205 = lean_ctor_get_uint8(x_25, 11);
lean_dec(x_25);
x_206 = 3;
x_207 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_207, 0, x_195);
lean_ctor_set_uint8(x_207, 1, x_196);
lean_ctor_set_uint8(x_207, 2, x_197);
lean_ctor_set_uint8(x_207, 3, x_198);
lean_ctor_set_uint8(x_207, 4, x_199);
lean_ctor_set_uint8(x_207, 5, x_200);
lean_ctor_set_uint8(x_207, 6, x_201);
lean_ctor_set_uint8(x_207, 7, x_202);
lean_ctor_set_uint8(x_207, 8, x_203);
lean_ctor_set_uint8(x_207, 9, x_206);
lean_ctor_set_uint8(x_207, 10, x_204);
lean_ctor_set_uint8(x_207, 11, x_205);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_ctor_set(x_2, 0, x_207);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_208 = l_Lean_Meta_mkDecide(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = 1;
x_212 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_212, 0, x_195);
lean_ctor_set_uint8(x_212, 1, x_196);
lean_ctor_set_uint8(x_212, 2, x_197);
lean_ctor_set_uint8(x_212, 3, x_198);
lean_ctor_set_uint8(x_212, 4, x_199);
lean_ctor_set_uint8(x_212, 5, x_200);
lean_ctor_set_uint8(x_212, 6, x_201);
lean_ctor_set_uint8(x_212, 7, x_202);
lean_ctor_set_uint8(x_212, 8, x_203);
lean_ctor_set_uint8(x_212, 9, x_211);
lean_ctor_set_uint8(x_212, 10, x_204);
lean_ctor_set_uint8(x_212, 11, x_205);
x_213 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_190);
lean_ctor_set(x_213, 2, x_191);
lean_ctor_set(x_213, 3, x_192);
lean_ctor_set(x_213, 4, x_193);
lean_ctor_set(x_213, 5, x_194);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_209);
x_214 = lean_whnf(x_209, x_213, x_3, x_4, x_5, x_210);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_219 = l_Lean_Expr_isConstOf(x_215, x_218);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_221 = l_Lean_Expr_isConstOf(x_215, x_220);
lean_dec(x_215);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_209);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_box(0);
if (lean_is_scalar(x_217)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_217;
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_216);
return x_223;
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_217);
x_224 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
lean_inc(x_4);
x_225 = l_Lean_Meta_mkEqRefl(x_224, x_2, x_3, x_4, x_5, x_216);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_4);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
x_229 = l_Lean_Expr_appArg_x21(x_209);
lean_dec(x_209);
x_230 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_231 = lean_array_push(x_230, x_1);
x_232 = lean_array_push(x_231, x_229);
x_233 = lean_array_push(x_232, x_226);
x_234 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_235 = l_Lean_mkAppN(x_234, x_233);
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_238 = lean_unsigned_to_nat(0u);
x_239 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_236);
lean_ctor_set(x_239, 2, x_238);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
if (lean_is_scalar(x_228)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_228;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_227);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_209);
lean_dec(x_1);
x_242 = lean_ctor_get(x_225, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_225, 1);
lean_inc(x_243);
lean_dec(x_225);
x_8 = x_242;
x_9 = x_243;
goto block_17;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_217);
lean_dec(x_215);
x_244 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
lean_inc(x_4);
x_245 = l_Lean_Meta_mkEqRefl(x_244, x_2, x_3, x_4, x_5, x_216);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_4);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_248 = x_245;
} else {
 lean_dec_ref(x_245);
 x_248 = lean_box(0);
}
x_249 = l_Lean_Expr_appArg_x21(x_209);
lean_dec(x_209);
x_250 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_251 = lean_array_push(x_250, x_1);
x_252 = lean_array_push(x_251, x_249);
x_253 = lean_array_push(x_252, x_246);
x_254 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_255 = l_Lean_mkAppN(x_254, x_253);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_258 = lean_unsigned_to_nat(0u);
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_256);
lean_ctor_set(x_259, 2, x_258);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
if (lean_is_scalar(x_248)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_248;
}
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_247);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_209);
lean_dec(x_1);
x_262 = lean_ctor_get(x_245, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_245, 1);
lean_inc(x_263);
lean_dec(x_245);
x_8 = x_262;
x_9 = x_263;
goto block_17;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_209);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_264 = lean_ctor_get(x_214, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_214, 1);
lean_inc(x_265);
lean_dec(x_214);
x_8 = x_264;
x_9 = x_265;
goto block_17;
}
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
lean_dec(x_2);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_266 = lean_ctor_get(x_208, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_208, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_268 = x_208;
} else {
 lean_dec_ref(x_208);
 x_268 = lean_box(0);
}
x_269 = l_Lean_Exception_isRuntime(x_266);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_266);
lean_dec(x_4);
x_270 = lean_box(0);
if (lean_is_scalar(x_268)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_268;
 lean_ctor_set_tag(x_271, 0);
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_267);
return x_271;
}
else
{
uint8_t x_272; 
x_272 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_272 == 0)
{
lean_object* x_273; 
if (lean_is_scalar(x_268)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_268;
}
lean_ctor_set(x_273, 0, x_266);
lean_ctor_set(x_273, 1, x_267);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_266);
x_274 = lean_box(0);
if (lean_is_scalar(x_268)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_268;
 lean_ctor_set_tag(x_275, 0);
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_267);
return x_275;
}
}
}
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; uint8_t x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_276 = lean_ctor_get(x_2, 0);
x_277 = lean_ctor_get(x_2, 1);
x_278 = lean_ctor_get(x_2, 2);
x_279 = lean_ctor_get(x_2, 3);
x_280 = lean_ctor_get(x_2, 4);
x_281 = lean_ctor_get(x_2, 5);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_2);
x_282 = lean_ctor_get_uint8(x_276, 0);
x_283 = lean_ctor_get_uint8(x_276, 1);
x_284 = lean_ctor_get_uint8(x_276, 2);
x_285 = lean_ctor_get_uint8(x_276, 3);
x_286 = lean_ctor_get_uint8(x_276, 4);
x_287 = lean_ctor_get_uint8(x_276, 5);
x_288 = lean_ctor_get_uint8(x_276, 6);
x_289 = lean_ctor_get_uint8(x_276, 7);
x_290 = lean_ctor_get_uint8(x_276, 8);
x_291 = lean_ctor_get_uint8(x_276, 10);
x_292 = lean_ctor_get_uint8(x_276, 11);
if (lean_is_exclusive(x_276)) {
 x_293 = x_276;
} else {
 lean_dec_ref(x_276);
 x_293 = lean_box(0);
}
x_294 = 3;
if (lean_is_scalar(x_293)) {
 x_295 = lean_alloc_ctor(0, 0, 12);
} else {
 x_295 = x_293;
}
lean_ctor_set_uint8(x_295, 0, x_282);
lean_ctor_set_uint8(x_295, 1, x_283);
lean_ctor_set_uint8(x_295, 2, x_284);
lean_ctor_set_uint8(x_295, 3, x_285);
lean_ctor_set_uint8(x_295, 4, x_286);
lean_ctor_set_uint8(x_295, 5, x_287);
lean_ctor_set_uint8(x_295, 6, x_288);
lean_ctor_set_uint8(x_295, 7, x_289);
lean_ctor_set_uint8(x_295, 8, x_290);
lean_ctor_set_uint8(x_295, 9, x_294);
lean_ctor_set_uint8(x_295, 10, x_291);
lean_ctor_set_uint8(x_295, 11, x_292);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
x_296 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_277);
lean_ctor_set(x_296, 2, x_278);
lean_ctor_set(x_296, 3, x_279);
lean_ctor_set(x_296, 4, x_280);
lean_ctor_set(x_296, 5, x_281);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_296);
lean_inc(x_1);
x_297 = l_Lean_Meta_mkDecide(x_1, x_296, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = 1;
x_301 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_301, 0, x_282);
lean_ctor_set_uint8(x_301, 1, x_283);
lean_ctor_set_uint8(x_301, 2, x_284);
lean_ctor_set_uint8(x_301, 3, x_285);
lean_ctor_set_uint8(x_301, 4, x_286);
lean_ctor_set_uint8(x_301, 5, x_287);
lean_ctor_set_uint8(x_301, 6, x_288);
lean_ctor_set_uint8(x_301, 7, x_289);
lean_ctor_set_uint8(x_301, 8, x_290);
lean_ctor_set_uint8(x_301, 9, x_300);
lean_ctor_set_uint8(x_301, 10, x_291);
lean_ctor_set_uint8(x_301, 11, x_292);
x_302 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_277);
lean_ctor_set(x_302, 2, x_278);
lean_ctor_set(x_302, 3, x_279);
lean_ctor_set(x_302, 4, x_280);
lean_ctor_set(x_302, 5, x_281);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_298);
x_303 = lean_whnf(x_298, x_302, x_3, x_4, x_5, x_299);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5;
x_308 = l_Lean_Expr_isConstOf(x_304, x_307);
if (x_308 == 0)
{
lean_object* x_309; uint8_t x_310; 
x_309 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7;
x_310 = l_Lean_Expr_isConstOf(x_304, x_309);
lean_dec(x_304);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_311 = lean_box(0);
if (lean_is_scalar(x_306)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_306;
}
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_305);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_306);
x_313 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8;
lean_inc(x_4);
x_314 = l_Lean_Meta_mkEqRefl(x_313, x_296, x_3, x_4, x_5, x_305);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_4);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_318 = l_Lean_Expr_appArg_x21(x_298);
lean_dec(x_298);
x_319 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_320 = lean_array_push(x_319, x_1);
x_321 = lean_array_push(x_320, x_318);
x_322 = lean_array_push(x_321, x_315);
x_323 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11;
x_324 = l_Lean_mkAppN(x_323, x_322);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3;
x_327 = lean_unsigned_to_nat(0u);
x_328 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_325);
lean_ctor_set(x_328, 2, x_327);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
if (lean_is_scalar(x_317)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_317;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_316);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_298);
lean_dec(x_1);
x_331 = lean_ctor_get(x_314, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_314, 1);
lean_inc(x_332);
lean_dec(x_314);
x_8 = x_331;
x_9 = x_332;
goto block_17;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_306);
lean_dec(x_304);
x_333 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13;
lean_inc(x_4);
x_334 = l_Lean_Meta_mkEqRefl(x_333, x_296, x_3, x_4, x_5, x_305);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_4);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_337 = x_334;
} else {
 lean_dec_ref(x_334);
 x_337 = lean_box(0);
}
x_338 = l_Lean_Expr_appArg_x21(x_298);
lean_dec(x_298);
x_339 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12;
x_340 = lean_array_push(x_339, x_1);
x_341 = lean_array_push(x_340, x_338);
x_342 = lean_array_push(x_341, x_335);
x_343 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17;
x_344 = l_Lean_mkAppN(x_343, x_342);
x_345 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_345, 0, x_344);
x_346 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14;
x_347 = lean_unsigned_to_nat(0u);
x_348 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_345);
lean_ctor_set(x_348, 2, x_347);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
if (lean_is_scalar(x_337)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_337;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_336);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_298);
lean_dec(x_1);
x_351 = lean_ctor_get(x_334, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_334, 1);
lean_inc(x_352);
lean_dec(x_334);
x_8 = x_351;
x_9 = x_352;
goto block_17;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; 
lean_dec(x_298);
lean_dec(x_296);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_353 = lean_ctor_get(x_303, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_303, 1);
lean_inc(x_354);
lean_dec(x_303);
x_8 = x_353;
x_9 = x_354;
goto block_17;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
lean_dec(x_296);
lean_dec(x_281);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_355 = lean_ctor_get(x_297, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_297, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_357 = x_297;
} else {
 lean_dec_ref(x_297);
 x_357 = lean_box(0);
}
x_358 = l_Lean_Exception_isRuntime(x_355);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_355);
lean_dec(x_4);
x_359 = lean_box(0);
if (lean_is_scalar(x_357)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_357;
 lean_ctor_set_tag(x_360, 0);
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_356);
return x_360;
}
else
{
uint8_t x_361; 
x_361 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_361 == 0)
{
lean_object* x_362; 
if (lean_is_scalar(x_357)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_357;
}
lean_ctor_set(x_362, 0, x_355);
lean_ctor_set(x_362, 1, x_356);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_355);
x_363 = lean_box(0);
if (lean_is_scalar(x_357)) {
 x_364 = lean_alloc_ctor(0, 2, 0);
} else {
 x_364 = x_357;
 lean_ctor_set_tag(x_364, 0);
}
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_364, 1, x_356);
return x_364;
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_365 = lean_box(0);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_6);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_box(0);
x_368 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_6);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = lean_box(0);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_6);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_371 = lean_box(0);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_6);
return x_372;
}
block_17:
{
uint8_t x_10; 
x_10 = l_Lean_Exception_isRuntime(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_ctor_get_uint8(x_4, sizeof(void*)*11);
lean_dec(x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f(x_1, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_21, 0, x_32);
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_38 = x_21;
} else {
 lean_dec_ref(x_21);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Simp_tryRewriteUsingDecide_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_Lean_Meta_Linear_simp_x3f(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_12, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_13, 0, x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_13);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_12, 0, x_29);
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_dec(x_12);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_ctor_set(x_13, 0, x_33);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_13);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_13, 0);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_41 = x_12;
} else {
 lean_dec_ref(x_12);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_45);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_41)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_41;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_12);
if (x_50 == 0)
{
return x_12;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
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
x_21 = l_Lean_Meta_Simp_simpArith_x3f___lambda__1(x_1, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
lean_dec(x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpArith_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_simpArith_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_32 = l_Std_Range_forIn_loop___at_Lean_Meta_Simp_simpMatchDiscrs_x3f___spec__1(x_21, x_24, x_28, x_26, x_28, x_14, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_33);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_32, 0);
lean_dec(x_37);
lean_ctor_set(x_32, 0, x_25);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_box(0);
x_43 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__1(x_24, x_28, x_41, x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_24);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
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
x_48 = !lean_is_exclusive(x_18);
if (x_48 == 0)
{
return x_18;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
x_50 = lean_ctor_get(x_18, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_18);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_array_uget(x_4, x_6);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_18);
x_19 = l_Lean_Meta_isRflTheorem(x_18, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
lean_inc(x_18);
x_23 = l_Lean_Expr_const___override(x_18, x_22);
x_24 = 1;
x_25 = 0;
x_26 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*1 + 1, x_25);
x_27 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore___closed__1;
x_28 = lean_unsigned_to_nat(1000u);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_25);
x_30 = lean_unbox(x_20);
lean_dec(x_20);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_30);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_11, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_11, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_11, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 5);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 2;
lean_ctor_set_uint8(x_31, 9, x_38);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_32);
lean_ctor_set(x_39, 2, x_33);
lean_ctor_set(x_39, 3, x_34);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_40 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_29, x_2, x_8, x_9, x_10, x_39, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; size_t x_43; size_t x_44; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = 1;
x_44 = lean_usize_add(x_6, x_43);
lean_inc(x_3);
{
size_t _tmp_5 = x_44;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_14 = x_42;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_15 = _tmp_14;
}
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_40, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_41, 0, x_50);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_41);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_40, 0, x_53);
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_40, 0, x_59);
return x_40;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_40, 1);
lean_inc(x_60);
lean_dec(x_40);
x_61 = lean_ctor_get(x_41, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_62 = x_41;
} else {
 lean_dec_ref(x_41);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_60);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_40);
if (x_69 == 0)
{
return x_40;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_40, 0);
x_71 = lean_ctor_get(x_40, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_40);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_73 = lean_ctor_get_uint8(x_31, 0);
x_74 = lean_ctor_get_uint8(x_31, 1);
x_75 = lean_ctor_get_uint8(x_31, 2);
x_76 = lean_ctor_get_uint8(x_31, 3);
x_77 = lean_ctor_get_uint8(x_31, 4);
x_78 = lean_ctor_get_uint8(x_31, 5);
x_79 = lean_ctor_get_uint8(x_31, 6);
x_80 = lean_ctor_get_uint8(x_31, 7);
x_81 = lean_ctor_get_uint8(x_31, 8);
x_82 = lean_ctor_get_uint8(x_31, 10);
x_83 = lean_ctor_get_uint8(x_31, 11);
lean_dec(x_31);
x_84 = 2;
x_85 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_85, 0, x_73);
lean_ctor_set_uint8(x_85, 1, x_74);
lean_ctor_set_uint8(x_85, 2, x_75);
lean_ctor_set_uint8(x_85, 3, x_76);
lean_ctor_set_uint8(x_85, 4, x_77);
lean_ctor_set_uint8(x_85, 5, x_78);
lean_ctor_set_uint8(x_85, 6, x_79);
lean_ctor_set_uint8(x_85, 7, x_80);
lean_ctor_set_uint8(x_85, 8, x_81);
lean_ctor_set_uint8(x_85, 9, x_84);
lean_ctor_set_uint8(x_85, 10, x_82);
lean_ctor_set_uint8(x_85, 11, x_83);
x_86 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_32);
lean_ctor_set(x_86, 2, x_33);
lean_ctor_set(x_86, 3, x_34);
lean_ctor_set(x_86, 4, x_35);
lean_ctor_set(x_86, 5, x_36);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_87 = l_Lean_Meta_Simp_tryTheorem_x3f(x_1, x_29, x_2, x_8, x_9, x_10, x_86, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; size_t x_90; size_t x_91; 
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = 1;
x_91 = lean_usize_add(x_6, x_90);
lean_inc(x_3);
{
size_t _tmp_5 = x_91;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_14 = x_89;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_15 = _tmp_14;
}
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_95);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(1, 1, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_94;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_93);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_87, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_105 = x_87;
} else {
 lean_dec_ref(x_87);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_19);
if (x_107 == 0)
{
return x_19;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_19, 0);
x_109 = lean_ctor_get(x_19, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_19);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatchCore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = lean_get_match_equations_for(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_array_get_size(x_15);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(x_2, x_3, x_20, x_15, x_18, x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_simpMatchCore_x3f___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_simpMatchCore_x3f(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_13);
x_14 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_24 = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(x_23, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_Simp_simpMatchCore_x3f(x_13, x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_24, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_25, 0, x_32);
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_24, 0, x_35);
return x_24;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_ctor_get(x_25, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_38 = x_25;
} else {
 lean_dec_ref(x_25);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_24);
if (x_42 == 0)
{
return x_24;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_24, 0);
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_24);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_11);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Meta_Simp_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 7);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_21 = l_Lean_Meta_reduceRecMatcher_x3f(x_2, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Simp_simpMatch_x3f___lambda__2(x_2, x_1, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
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
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_box(0);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_22, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_22, 0);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_box(0);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_21, 0, x_39);
return x_21;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 x_42 = x_22;
} else {
 lean_dec_ref(x_22);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_42)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_42;
}
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getMatcherInfo_x3f___at_Lean_Meta_Simp_simpMatch_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_simpMatch_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpMatch_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_simpMatch_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_19 = lean_array_uget(x_5, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 4);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_20, x_21, x_2, x_22, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_7, x_26);
lean_inc(x_4);
{
size_t _tmp_6 = x_27;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_15 = x_25;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_16 = _tmp_15;
}
goto _start;
}
else
{
uint8_t x_29; 
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
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_24, 0, x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_23, 0, x_40);
return x_23;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_ctor_get(x_24, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_43 = x_24;
} else {
 lean_dec_ref(x_24);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
}
}
else
{
uint8_t x_49; 
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
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(x_1, x_2, x_3, x_17, x_12, x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Simp_rewritePre___lambda__1(x_1, x_13, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1(x_1, x_2, x_17, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_rewritePre___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_Simp_rewritePre(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_19 = lean_array_uget(x_5, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 4);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Meta_Simp_rewrite_x3f(x_1, x_20, x_21, x_2, x_22, x_3, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_7, x_26);
lean_inc(x_4);
{
size_t _tmp_6 = x_27;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_15 = x_25;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_16 = _tmp_15;
}
goto _start;
}
else
{
uint8_t x_29; 
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
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_23, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_24, 0, x_33);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_23, 0, x_35);
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_24, 0);
lean_inc(x_36);
lean_dec(x_24);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_23, 0, x_40);
return x_23;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_ctor_get(x_24, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_43 = x_24;
} else {
 lean_dec_ref(x_24);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_42);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
}
}
else
{
uint8_t x_49; 
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
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = lean_array_get_size(x_12);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = l_Lean_Meta_Simp_rewrite_x3f___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_18 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(x_1, x_2, x_3, x_17, x_12, x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Simp_rewritePre___lambda__1(x_1, x_13, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_26);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
x_32 = lean_ctor_get(x_18, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1(x_1, x_2, x_17, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_rewritePost___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_Simp_rewritePost(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_preDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Meta_Simp_rewritePre(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_13, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_110 = l_Lean_Meta_Simp_simpMatch_x3f(x_2, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_dec(x_108);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_16 = x_13;
x_17 = x_112;
goto block_107;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_13);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
x_115 = l_Lean_Meta_Simp_Step_result(x_114);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_116 = l_Lean_Meta_Simp_mkEqTrans(x_108, x_115, x_6, x_7, x_8, x_9, x_113);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Meta_Simp_Step_updateResult(x_114, x_117);
x_16 = x_119;
x_17 = x_118;
goto block_107;
}
else
{
uint8_t x_120; 
lean_dec(x_114);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_116);
if (x_120 == 0)
{
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 0);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_116);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_108);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_110);
if (x_124 == 0)
{
return x_110;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_110, 0);
x_126 = lean_ctor_get(x_110, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_110);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
x_16 = x_13;
x_17 = x_14;
goto block_107;
}
block_107:
{
lean_object* x_18; lean_object* x_19; 
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_16, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_89 = l_Lean_Meta_Simp_preSimproc_x3f(x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
lean_dec(x_87);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_18 = x_16;
x_19 = x_91;
goto block_86;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_16);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = l_Lean_Meta_Simp_Step_result(x_93);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_95 = l_Lean_Meta_Simp_mkEqTrans(x_87, x_94, x_6, x_7, x_8, x_9, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Meta_Simp_Step_updateResult(x_93, x_96);
x_18 = x_98;
x_19 = x_97;
goto block_86;
}
else
{
uint8_t x_99; 
lean_dec(x_93);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_87);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_89);
if (x_103 == 0)
{
return x_89;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_89, 0);
x_105 = lean_ctor_get(x_89, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_89);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
x_18 = x_16;
x_19 = x_17;
goto block_86;
}
block_86:
{
lean_object* x_20; lean_object* x_21; 
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_50 = lean_ctor_get(x_18, 0);
lean_inc(x_50);
x_64 = lean_ctor_get(x_50, 0);
lean_inc(x_64);
x_65 = l_Lean_Meta_Simp_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_66, sizeof(void*)*2 + 9);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_box(0);
x_51 = x_69;
x_52 = x_68;
goto block_63;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_71 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f(x_64, x_6, x_7, x_8, x_9, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(0);
x_51 = x_74;
x_52 = x_73;
goto block_63;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_72, 0, x_78);
x_51 = x_72;
x_52 = x_75;
goto block_63;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 0);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_51 = x_81;
x_52 = x_75;
goto block_63;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_50);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_71);
if (x_82 == 0)
{
return x_71;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_71, 0);
x_84 = lean_ctor_get(x_71, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_71);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
block_63:
{
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_50);
x_20 = x_18;
x_21 = x_52;
goto block_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_18);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_Simp_Step_result(x_53);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_55 = l_Lean_Meta_Simp_mkEqTrans(x_50, x_54, x_6, x_7, x_8, x_9, x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Meta_Simp_Step_updateResult(x_53, x_56);
x_20 = x_58;
x_21 = x_57;
goto block_49;
}
else
{
uint8_t x_59; 
lean_dec(x_53);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
x_20 = x_18;
x_21 = x_19;
goto block_49;
}
block_49:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Meta_Simp_Step_result(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_expr_eqv(x_23, x_1);
lean_dec(x_1);
lean_dec(x_23);
if (x_24 == 0)
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_Simp_preDefault(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_Simp_Step_result(x_28);
x_31 = l_Lean_Meta_Simp_mkEqTrans(x_25, x_30, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_Meta_Simp_Step_updateResult(x_28, x_33);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = l_Lean_Meta_Simp_Step_updateResult(x_28, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_28);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
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
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_15)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_15;
}
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_21);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_15)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_15;
}
lean_ctor_set(x_48, 0, x_20);
lean_ctor_set(x_48, 1, x_21);
return x_48;
}
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_12);
if (x_128 == 0)
{
return x_12;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_12, 0);
x_130 = lean_ctor_get(x_12, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_12);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_postDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_Simp_rewritePost(x_1, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_13, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_127 = l_Lean_Meta_Simp_simpArith_x3f(x_126, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec(x_125);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_16 = x_13;
x_17 = x_129;
goto block_124;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_13);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec(x_128);
x_132 = l_Lean_Meta_Simp_Step_result(x_131);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_133 = l_Lean_Meta_Simp_mkEqTrans(x_125, x_132, x_6, x_7, x_8, x_9, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_Simp_Step_updateResult(x_131, x_134);
x_16 = x_136;
x_17 = x_135;
goto block_124;
}
else
{
uint8_t x_137; 
lean_dec(x_131);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = !lean_is_exclusive(x_133);
if (x_137 == 0)
{
return x_133;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_133, 0);
x_139 = lean_ctor_get(x_133, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_133);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_125);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = !lean_is_exclusive(x_127);
if (x_141 == 0)
{
return x_127;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_127, 0);
x_143 = lean_ctor_get(x_127, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_127);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
x_16 = x_13;
x_17 = x_14;
goto block_124;
}
block_124:
{
lean_object* x_18; lean_object* x_19; 
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_16, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_106 = l_Lean_Meta_Simp_postSimproc_x3f(x_105, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_104);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_18 = x_16;
x_19 = x_108;
goto block_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_16);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_111 = l_Lean_Meta_Simp_Step_result(x_110);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_112 = l_Lean_Meta_Simp_mkEqTrans(x_104, x_111, x_6, x_7, x_8, x_9, x_109);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Meta_Simp_Step_updateResult(x_110, x_113);
x_18 = x_115;
x_19 = x_114;
goto block_103;
}
else
{
uint8_t x_116; 
lean_dec(x_110);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = !lean_is_exclusive(x_112);
if (x_116 == 0)
{
return x_112;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_112, 0);
x_118 = lean_ctor_get(x_112, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_112);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_104);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = !lean_is_exclusive(x_106);
if (x_120 == 0)
{
return x_106;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_106, 0);
x_122 = lean_ctor_get(x_106, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_106);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_dec(x_3);
x_18 = x_16;
x_19 = x_17;
goto block_103;
}
block_103:
{
lean_object* x_20; lean_object* x_21; 
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_67 = lean_ctor_get(x_18, 0);
lean_inc(x_67);
x_81 = lean_ctor_get(x_67, 0);
lean_inc(x_81);
x_82 = l_Lean_Meta_Simp_getConfig___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_5);
lean_dec(x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*2 + 9);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_81);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_box(0);
x_68 = x_86;
x_69 = x_85;
goto block_80;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_dec(x_82);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_88 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f(x_81, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(0);
x_68 = x_91;
x_69 = x_90;
goto block_80;
}
else
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = !lean_is_exclusive(x_89);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_89, 0);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_89, 0, x_95);
x_68 = x_89;
x_69 = x_92;
goto block_80;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
lean_dec(x_89);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_68 = x_98;
x_69 = x_92;
goto block_80;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_67);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_99 = !lean_is_exclusive(x_88);
if (x_99 == 0)
{
return x_88;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_88, 0);
x_101 = lean_ctor_get(x_88, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_88);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
block_80:
{
if (lean_obj_tag(x_68) == 0)
{
lean_dec(x_67);
x_20 = x_18;
x_21 = x_69;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_18);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_Simp_Step_result(x_70);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_72 = l_Lean_Meta_Simp_mkEqTrans(x_67, x_71, x_6, x_7, x_8, x_9, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Meta_Simp_Step_updateResult(x_70, x_73);
x_20 = x_75;
x_21 = x_74;
goto block_66;
}
else
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
x_20 = x_18;
x_21 = x_19;
goto block_66;
}
block_66:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_Simp_rewriteCtorEq_x3f(x_23, x_6, x_7, x_8, x_9, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_20);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_20, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_33);
x_34 = l_Lean_Meta_Simp_Step_result(x_20);
x_35 = l_Lean_Meta_Simp_mkEqTrans(x_22, x_34, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_Lean_Meta_Simp_Step_updateResult(x_20, x_37);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = l_Lean_Meta_Simp_Step_updateResult(x_20, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_20);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_20);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec(x_24);
x_48 = lean_ctor_get(x_25, 0);
lean_inc(x_48);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Meta_Simp_Step_result(x_49);
x_51 = l_Lean_Meta_Simp_mkEqTrans(x_22, x_50, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Meta_Simp_Step_updateResult(x_49, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_49);
x_57 = lean_ctor_get(x_51, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_59 = x_51;
} else {
 lean_dec_ref(x_51);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_24);
if (x_61 == 0)
{
return x_24;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_24, 0);
x_63 = lean_ctor_get(x_24, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_24);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_15)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_15;
}
lean_ctor_set(x_65, 0, x_20);
lean_ctor_set(x_65, 1, x_21);
return x_65;
}
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_145 = !lean_is_exclusive(x_12);
if (x_145 == 0)
{
return x_12;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_12, 0);
x_147 = lean_ctor_get(x_12, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_12);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis_go(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Expr_isEq(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isHEq(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_expr_has_loose_bvar(x_3, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
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
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_consumeMData(x_1);
x_13 = l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2;
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec(x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isEqnThmHypothesis_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis_go(x_1);
lean_dec(x_1);
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
lean_dec(x_1);
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
x_3 = lean_unsigned_to_nat(360u);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_13, 1);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_nat_dec_le(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_18, x_19);
lean_dec(x_18);
lean_ctor_set(x_6, 4, x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = lean_simp(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = l_Lean_Expr_consumeMData(x_25);
lean_dec(x_25);
x_27 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_28 = l_Lean_Expr_isConstOf(x_26, x_27);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_box(0);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; 
lean_free_object(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = l_Lean_Meta_Simp_Result_getProof(x_23, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_10);
x_33 = l_Lean_Meta_mkOfEqTrue(x_31, x_8, x_9, x_10, x_11, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = l_Lean_Exception_isRuntime(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
lean_dec(x_10);
x_44 = lean_box(0);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
else
{
uint8_t x_45; 
x_45 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; 
lean_dec(x_42);
x_46 = lean_box(0);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_46);
return x_33;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_33);
x_49 = l_Lean_Exception_isRuntime(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_10);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
else
{
uint8_t x_52; 
x_52 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_48);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
return x_55;
}
}
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_30, 0);
x_58 = l_Lean_Exception_isRuntime(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_dec(x_10);
x_59 = lean_box(0);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_59);
return x_30;
}
else
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_60 == 0)
{
return x_30;
}
else
{
lean_object* x_61; 
lean_dec(x_57);
x_61 = lean_box(0);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_61);
return x_30;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_30, 0);
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_30);
x_64 = l_Lean_Exception_isRuntime(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_10);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
uint8_t x_67; 
x_67 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_62);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = l_Lean_Expr_consumeMData(x_73);
lean_dec(x_73);
x_75 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_76 = l_Lean_Expr_isConstOf(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_71);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
else
{
lean_object* x_79; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_79 = l_Lean_Meta_Simp_Result_getProof(x_71, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_10);
x_82 = l_Lean_Meta_mkOfEqTrue(x_80, x_8, x_9, x_10, x_11, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_10);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_83);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_82, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_90 = x_82;
} else {
 lean_dec_ref(x_82);
 x_90 = lean_box(0);
}
x_91 = l_Lean_Exception_isRuntime(x_88);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_10);
x_92 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
 lean_ctor_set_tag(x_93, 0);
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_94 == 0)
{
lean_object* x_95; 
if (lean_is_scalar(x_90)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_90;
}
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_89);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_88);
x_96 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_90;
 lean_ctor_set_tag(x_97, 0);
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_89);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_98 = lean_ctor_get(x_79, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_79, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_100 = x_79;
} else {
 lean_dec_ref(x_79);
 x_100 = lean_box(0);
}
x_101 = l_Lean_Exception_isRuntime(x_98);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_98);
lean_dec(x_10);
x_102 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
 lean_ctor_set_tag(x_103, 0);
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_104 == 0)
{
lean_object* x_105; 
if (lean_is_scalar(x_100)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_100;
}
lean_ctor_set(x_105, 0, x_98);
lean_ctor_set(x_105, 1, x_99);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_98);
x_106 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_100;
 lean_ctor_set_tag(x_107, 0);
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_99);
return x_107;
}
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_108 = !lean_is_exclusive(x_21);
if (x_108 == 0)
{
return x_21;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_21, 0);
x_110 = lean_ctor_get(x_21, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_21);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_6, 0);
x_113 = lean_ctor_get(x_6, 1);
x_114 = lean_ctor_get(x_6, 2);
x_115 = lean_ctor_get(x_6, 3);
x_116 = lean_ctor_get(x_6, 4);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_6);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_116, x_117);
lean_dec(x_116);
x_119 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_119, 0, x_112);
lean_ctor_set(x_119, 1, x_113);
lean_ctor_set(x_119, 2, x_114);
lean_ctor_set(x_119, 3, x_115);
lean_ctor_set(x_119, 4, x_118);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_120 = lean_simp(x_2, x_5, x_119, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
x_125 = l_Lean_Expr_consumeMData(x_124);
lean_dec(x_124);
x_126 = l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2;
x_127 = l_Lean_Expr_isConstOf(x_125, x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_121);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_128 = lean_box(0);
if (lean_is_scalar(x_123)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_123;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_122);
return x_129;
}
else
{
lean_object* x_130; 
lean_dec(x_123);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_130 = l_Lean_Meta_Simp_Result_getProof(x_121, x_8, x_9, x_10, x_11, x_122);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_10);
x_133 = l_Lean_Meta_mkOfEqTrue(x_131, x_8, x_9, x_10, x_11, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_10);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_134);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_133, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_133, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_141 = x_133;
} else {
 lean_dec_ref(x_133);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Exception_isRuntime(x_139);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_139);
lean_dec(x_10);
x_143 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_141;
 lean_ctor_set_tag(x_144, 0);
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_140);
return x_144;
}
else
{
uint8_t x_145; 
x_145 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_145 == 0)
{
lean_object* x_146; 
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_141;
}
lean_ctor_set(x_146, 0, x_139);
lean_ctor_set(x_146, 1, x_140);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_139);
x_147 = lean_box(0);
if (lean_is_scalar(x_141)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_141;
 lean_ctor_set_tag(x_148, 0);
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
return x_148;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
x_149 = lean_ctor_get(x_130, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_130, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_151 = x_130;
} else {
 lean_dec_ref(x_130);
 x_151 = lean_box(0);
}
x_152 = l_Lean_Exception_isRuntime(x_149);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_149);
lean_dec(x_10);
x_153 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_151;
 lean_ctor_set_tag(x_154, 0);
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_150);
return x_154;
}
else
{
uint8_t x_155; 
x_155 = lean_ctor_get_uint8(x_10, sizeof(void*)*11);
lean_dec(x_10);
if (x_155 == 0)
{
lean_object* x_156; 
if (lean_is_scalar(x_151)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_151;
}
lean_ctor_set(x_156, 0, x_149);
lean_ctor_set(x_156, 1, x_150);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_149);
x_157 = lean_box(0);
if (lean_is_scalar(x_151)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_151;
 lean_ctor_set_tag(x_158, 0);
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_150);
return x_158;
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_159 = lean_ctor_get(x_120, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_120, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_161 = x_120;
} else {
 lean_dec_ref(x_120);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
lean_dec(x_2);
lean_inc(x_3);
x_163 = l_Lean_isTracingEnabledFor___at_Lean_Meta_Simp_congrArgs___spec__1(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l___private_Lean_Meta_Tactic_Simp_Rewrite_0__Lean_Meta_Simp_tryTheoremCore_go___lambda__4___closed__1;
x_167 = lean_unbox(x_164);
lean_dec(x_164);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_3);
x_168 = lean_box(0);
x_169 = lean_apply_9(x_166, x_168, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__1___closed__2;
x_171 = l_Lean_addTrace___at_Lean_Meta_Simp_congrArgs___spec__2(x_3, x_170, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_165);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_apply_9(x_166, x_172, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_173);
return x_174;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(">> discharge\?: ", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
x_20 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__2;
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
lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Meta_Simp_dischargeUsingAssumption_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__3(x_1, x_10, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_26 = x_15;
} else {
 lean_dec_ref(x_15);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(1, 1, 0);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_11 = l_Lean_Meta_Simp_postDefault(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods___elambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_preDefault(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkMethods(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_inc(x_2);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkMethods___elambda__2), 10, 1);
lean_closure_set(x_3, 0, x_2);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkMethods___elambda__1), 10, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
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
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_mkDefaultMethods___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Instances_erased___default___spec__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_mkDefaultMethods___closed__3;
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
x_7 = l_Lean_Meta_Simp_mkDefaultMethods___closed__4;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
x_13 = l_Lean_Meta_Simp_mkMethods(x_11, x_12);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1;
x_17 = l_Lean_Meta_Simp_mkMethods(x_14, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
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
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__1);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__2);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__3);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___lambda__1___closed__4);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__1);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__2);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__3);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__4);
l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5 = _init_l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteCtorEq_x3f___closed__5);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__1);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__2);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__3);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__4);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__5);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__6);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__7);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__8);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__9);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__10);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__11);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__12);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__13);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__14);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__15);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__16);
l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17 = _init_l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_rewriteUsingDecide_x3f___closed__17);
l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_simpMatchDiscrs_x3f___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePre___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_Simp_rewritePost___spec__1___closed__1);
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
l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__1);
l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_dischargeDefault_x3f___lambda__2___closed__2);
l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1 = _init_l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethodsCore___closed__1);
l_Lean_Meta_Simp_mkDefaultMethods___closed__1 = _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethods___closed__1);
l_Lean_Meta_Simp_mkDefaultMethods___closed__2 = _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethods___closed__2);
l_Lean_Meta_Simp_mkDefaultMethods___closed__3 = _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethods___closed__3);
l_Lean_Meta_Simp_mkDefaultMethods___closed__4 = _init_l_Lean_Meta_Simp_mkDefaultMethods___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_mkDefaultMethods___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
