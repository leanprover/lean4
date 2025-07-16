// Lean compiler output
// Module: Lean.Meta.Tactic.Split
// Imports: Lean.Meta.Match.MatcherApp.Basic Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.SplitIf Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Generalize
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
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__15;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceRecMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch_pre___closed__0;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__1;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__1;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isDIte(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___boxed(lean_object**);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__5;
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0;
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3;
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6717_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__11;
static lean_object* l_Lean_Meta_Split_isDiscrGenException___closed__0;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__1;
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_introNCore_spec__4(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_881_;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2;
lean_object* l_Lean_Meta_generalizeTargetsEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__0;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_881_(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__14;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3;
static lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__0;
static uint64_t l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__2;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2;
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6717_;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6717_(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__2;
static lean_object* l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3;
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__0;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_delabDelayedAssignedMVar_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__4;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__3;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__7;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__4;
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__9;
static lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__0;
lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__2;
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__7;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitIfLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1;
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_881_;
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__3;
uint64_t l_Lean_Expr_hash(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__10;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__6;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__4;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__1;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_x3f(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6717_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatchEqns_size(lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1;
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6717_;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6717_;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8;
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__0;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6717_;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findSplit_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l_Lean_Meta_Split_simpMatch___closed__3;
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Meta_isMatcherAppCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__2;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__1;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__0;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__1;
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__1;
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6717_;
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_hasForwardDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1;
static lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6717_;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6717_;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_Split_isDiscrGenException(lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_discrGenExId;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_isDiscrGenException___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1;
lean_object* l_Array_zip___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6717_;
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__2;
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1;
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__0;
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___boxed(lean_object**);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0;
static lean_object* l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6717_;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__12;
static lean_object* _init_l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_Simp_neutralConfig;
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = 1;
x_10 = 0;
x_11 = 2;
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 1, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 2, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 3, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 4, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 5, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_11);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 8, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 9, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 10, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 11, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 12, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 13, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 14, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 15, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 16, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 17, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 18, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 19, x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 20, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 21, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 22, x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 23, x_9);
x_12 = l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0;
x_13 = l_Lean_Meta_Simp_mkContext___redArg(x_7, x_12, x_5, x_1, x_2, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = 1;
x_17 = 0;
x_18 = 2;
x_19 = lean_alloc_ctor(0, 2, 24);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 1, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 2, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 3, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 4, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 5, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 6, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 7, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 9, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 10, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 11, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 12, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 13, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 14, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 15, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 16, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 17, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 18, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 19, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 20, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 21, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 22, x_16);
lean_ctor_set_uint8(x_19, sizeof(void*)*2 + 23, x_16);
x_20 = l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0;
x_21 = l_Lean_Meta_Simp_mkContext___redArg(x_19, x_20, x_5, x_1, x_2, x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Split_getSimpMatchContext___redArg(x_1, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Split_getSimpMatchContext___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Split_getSimpMatchContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_isMatcherAppCore(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_isMatcherAppCore(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg(x_1, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch_pre___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg(x_1, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = l_Lean_Meta_Split_simpMatch_pre___closed__0;
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l_Lean_Meta_Split_simpMatch_pre___closed__0;
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
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_reduceRecMatcher_x3f(x_1, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Expr_getAppFn(x_1);
x_24 = l_Lean_Expr_constName_x21(x_23);
lean_dec_ref(x_23);
x_25 = l_Lean_Meta_Simp_simpMatchCore(x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_32);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_31);
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_36);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_20, 0, x_37);
return x_20;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_40 = x_21;
} else {
 lean_dec_ref(x_21);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_unbox(x_11);
lean_dec(x_11);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_43);
if (lean_is_scalar(x_40)) {
 x_44 = lean_alloc_ctor(0, 1, 0);
} else {
 x_44 = x_40;
 lean_ctor_set_tag(x_44, 0);
}
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_20);
if (x_46 == 0)
{
return x_20;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_20, 0);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_20);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = 1;
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_Split_simpMatch___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Split_simpMatch___closed__4;
x_4 = l_Lean_Meta_Split_simpMatch___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__6;
x_2 = l_Lean_Meta_Split_simpMatch___closed__3;
x_3 = l_Lean_Meta_Split_simpMatch___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Split_simpMatch___closed__7;
x_2 = l_Lean_Meta_Split_simpMatch___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_simpMatch___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch_pre), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_7 = 0;
lean_inc_ref(x_2);
x_8 = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(x_7, x_2, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l_Lean_Meta_Split_getSimpMatchContext___redArg(x_2, x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__0___boxed), 9, 0);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__1___boxed), 9, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__2___boxed), 9, 0);
x_17 = l_Lean_Meta_Split_simpMatch___closed__8;
x_18 = l_Lean_Meta_Split_simpMatch___closed__9;
x_19 = 1;
x_20 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*5, x_19);
x_21 = l_Lean_Meta_Simp_main(x_1, x_12, x_17, x_20, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
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
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
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
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_8, x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_11);
x_13 = l_Lean_Meta_Split_simpMatch(x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_Meta_applySimpResultToTarget(x_1, x_11, x_14, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_11);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatchTarget___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_22; 
x_22 = l_Lean_Expr_isAppOf(x_3, x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_23 = l_Lean_Meta_Split_simpMatch_pre___closed__0;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_3);
x_25 = l_Lean_Meta_reduceRecMatcher_x3f(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_2);
x_28 = l_Lean_Meta_isRflTheorem(x_2, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
uint64_t x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_34 = lean_ctor_get(x_7, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; lean_object* x_50; 
x_36 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
x_37 = lean_box(0);
lean_inc(x_2);
x_38 = l_Lean_Expr_const___override(x_2, x_37);
x_39 = lean_unsigned_to_nat(1000u);
x_40 = 0;
x_41 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_40);
x_42 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*5, x_22);
lean_ctor_set_uint8(x_42, sizeof(void*)*5 + 1, x_40);
x_43 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_42, sizeof(void*)*5 + 2, x_43);
x_44 = 2;
lean_ctor_set_uint8(x_29, 9, x_44);
x_45 = 2;
x_46 = lean_uint64_shift_right(x_33, x_45);
x_47 = lean_uint64_shift_left(x_46, x_45);
x_48 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_49 = lean_uint64_lor(x_47, x_48);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_49);
x_50 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_42, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_12 = x_51;
x_13 = x_52;
goto block_21;
}
else
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
lean_dec_ref(x_50);
x_12 = x_53;
x_13 = x_54;
goto block_21;
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_91; lean_object* x_92; 
x_59 = lean_ctor_get_uint8(x_29, 0);
x_60 = lean_ctor_get_uint8(x_29, 1);
x_61 = lean_ctor_get_uint8(x_29, 2);
x_62 = lean_ctor_get_uint8(x_29, 3);
x_63 = lean_ctor_get_uint8(x_29, 4);
x_64 = lean_ctor_get_uint8(x_29, 5);
x_65 = lean_ctor_get_uint8(x_29, 6);
x_66 = lean_ctor_get_uint8(x_29, 7);
x_67 = lean_ctor_get_uint8(x_29, 8);
x_68 = lean_ctor_get_uint8(x_29, 10);
x_69 = lean_ctor_get_uint8(x_29, 11);
x_70 = lean_ctor_get_uint8(x_29, 12);
x_71 = lean_ctor_get_uint8(x_29, 13);
x_72 = lean_ctor_get_uint8(x_29, 14);
x_73 = lean_ctor_get_uint8(x_29, 15);
x_74 = lean_ctor_get_uint8(x_29, 16);
x_75 = lean_ctor_get_uint8(x_29, 17);
x_76 = lean_ctor_get_uint8(x_29, 18);
lean_dec(x_29);
x_77 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
x_78 = lean_box(0);
lean_inc(x_2);
x_79 = l_Lean_Expr_const___override(x_2, x_78);
x_80 = lean_unsigned_to_nat(1000u);
x_81 = 0;
x_82 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set_uint8(x_82, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_82, sizeof(void*)*1 + 1, x_81);
x_83 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_79);
lean_ctor_set(x_83, 3, x_80);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*5, x_22);
lean_ctor_set_uint8(x_83, sizeof(void*)*5 + 1, x_81);
x_84 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_83, sizeof(void*)*5 + 2, x_84);
x_85 = 2;
x_86 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_86, 0, x_59);
lean_ctor_set_uint8(x_86, 1, x_60);
lean_ctor_set_uint8(x_86, 2, x_61);
lean_ctor_set_uint8(x_86, 3, x_62);
lean_ctor_set_uint8(x_86, 4, x_63);
lean_ctor_set_uint8(x_86, 5, x_64);
lean_ctor_set_uint8(x_86, 6, x_65);
lean_ctor_set_uint8(x_86, 7, x_66);
lean_ctor_set_uint8(x_86, 8, x_67);
lean_ctor_set_uint8(x_86, 9, x_85);
lean_ctor_set_uint8(x_86, 10, x_68);
lean_ctor_set_uint8(x_86, 11, x_69);
lean_ctor_set_uint8(x_86, 12, x_70);
lean_ctor_set_uint8(x_86, 13, x_71);
lean_ctor_set_uint8(x_86, 14, x_72);
lean_ctor_set_uint8(x_86, 15, x_73);
lean_ctor_set_uint8(x_86, 16, x_74);
lean_ctor_set_uint8(x_86, 17, x_75);
lean_ctor_set_uint8(x_86, 18, x_76);
x_87 = 2;
x_88 = lean_uint64_shift_right(x_33, x_87);
x_89 = lean_uint64_shift_left(x_88, x_87);
x_90 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_91 = lean_uint64_lor(x_89, x_90);
lean_ctor_set(x_7, 0, x_86);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_91);
x_92 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec_ref(x_92);
x_12 = x_93;
x_13 = x_94;
goto block_21;
}
else
{
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec_ref(x_92);
x_12 = x_95;
x_13 = x_96;
goto block_21;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
else
{
uint64_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; lean_object* x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; lean_object* x_145; lean_object* x_146; 
x_101 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_102 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_103 = lean_ctor_get(x_7, 1);
x_104 = lean_ctor_get(x_7, 2);
x_105 = lean_ctor_get(x_7, 3);
x_106 = lean_ctor_get(x_7, 4);
x_107 = lean_ctor_get(x_7, 5);
x_108 = lean_ctor_get(x_7, 6);
x_109 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_110 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_7);
x_111 = lean_ctor_get_uint8(x_29, 0);
x_112 = lean_ctor_get_uint8(x_29, 1);
x_113 = lean_ctor_get_uint8(x_29, 2);
x_114 = lean_ctor_get_uint8(x_29, 3);
x_115 = lean_ctor_get_uint8(x_29, 4);
x_116 = lean_ctor_get_uint8(x_29, 5);
x_117 = lean_ctor_get_uint8(x_29, 6);
x_118 = lean_ctor_get_uint8(x_29, 7);
x_119 = lean_ctor_get_uint8(x_29, 8);
x_120 = lean_ctor_get_uint8(x_29, 10);
x_121 = lean_ctor_get_uint8(x_29, 11);
x_122 = lean_ctor_get_uint8(x_29, 12);
x_123 = lean_ctor_get_uint8(x_29, 13);
x_124 = lean_ctor_get_uint8(x_29, 14);
x_125 = lean_ctor_get_uint8(x_29, 15);
x_126 = lean_ctor_get_uint8(x_29, 16);
x_127 = lean_ctor_get_uint8(x_29, 17);
x_128 = lean_ctor_get_uint8(x_29, 18);
if (lean_is_exclusive(x_29)) {
 x_129 = x_29;
} else {
 lean_dec_ref(x_29);
 x_129 = lean_box(0);
}
x_130 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
x_131 = lean_box(0);
lean_inc(x_2);
x_132 = l_Lean_Expr_const___override(x_2, x_131);
x_133 = lean_unsigned_to_nat(1000u);
x_134 = 0;
x_135 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_135, 0, x_2);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_22);
lean_ctor_set_uint8(x_135, sizeof(void*)*1 + 1, x_134);
x_136 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_136, 0, x_130);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_132);
lean_ctor_set(x_136, 3, x_133);
lean_ctor_set(x_136, 4, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*5, x_22);
lean_ctor_set_uint8(x_136, sizeof(void*)*5 + 1, x_134);
x_137 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_136, sizeof(void*)*5 + 2, x_137);
x_138 = 2;
if (lean_is_scalar(x_129)) {
 x_139 = lean_alloc_ctor(0, 0, 19);
} else {
 x_139 = x_129;
}
lean_ctor_set_uint8(x_139, 0, x_111);
lean_ctor_set_uint8(x_139, 1, x_112);
lean_ctor_set_uint8(x_139, 2, x_113);
lean_ctor_set_uint8(x_139, 3, x_114);
lean_ctor_set_uint8(x_139, 4, x_115);
lean_ctor_set_uint8(x_139, 5, x_116);
lean_ctor_set_uint8(x_139, 6, x_117);
lean_ctor_set_uint8(x_139, 7, x_118);
lean_ctor_set_uint8(x_139, 8, x_119);
lean_ctor_set_uint8(x_139, 9, x_138);
lean_ctor_set_uint8(x_139, 10, x_120);
lean_ctor_set_uint8(x_139, 11, x_121);
lean_ctor_set_uint8(x_139, 12, x_122);
lean_ctor_set_uint8(x_139, 13, x_123);
lean_ctor_set_uint8(x_139, 14, x_124);
lean_ctor_set_uint8(x_139, 15, x_125);
lean_ctor_set_uint8(x_139, 16, x_126);
lean_ctor_set_uint8(x_139, 17, x_127);
lean_ctor_set_uint8(x_139, 18, x_128);
x_140 = 2;
x_141 = lean_uint64_shift_right(x_101, x_140);
x_142 = lean_uint64_shift_left(x_141, x_140);
x_143 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_144 = lean_uint64_lor(x_142, x_143);
x_145 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_103);
lean_ctor_set(x_145, 2, x_104);
lean_ctor_set(x_145, 3, x_105);
lean_ctor_set(x_145, 4, x_106);
lean_ctor_set(x_145, 5, x_107);
lean_ctor_set(x_145, 6, x_108);
lean_ctor_set_uint64(x_145, sizeof(void*)*7, x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*7 + 8, x_102);
lean_ctor_set_uint8(x_145, sizeof(void*)*7 + 9, x_109);
lean_ctor_set_uint8(x_145, sizeof(void*)*7 + 10, x_110);
x_146 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_136, x_4, x_5, x_6, x_145, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec_ref(x_146);
x_12 = x_147;
x_13 = x_148;
goto block_21;
}
else
{
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_dec_ref(x_146);
x_12 = x_149;
x_13 = x_150;
goto block_21;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_146, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_153 = x_146;
} else {
 lean_dec_ref(x_146);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_155 = !lean_is_exclusive(x_28);
if (x_155 == 0)
{
return x_28;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_28, 0);
x_157 = lean_ctor_get(x_28, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_28);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_25);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_25, 0);
lean_dec(x_160);
x_161 = !lean_is_exclusive(x_26);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_26, 0);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set_uint8(x_164, sizeof(void*)*2, x_22);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_164);
return x_25;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_26, 0);
lean_inc(x_165);
lean_dec(x_26);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
lean_ctor_set_uint8(x_167, sizeof(void*)*2, x_22);
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_25, 0, x_168);
return x_25;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_25, 1);
lean_inc(x_169);
lean_dec(x_25);
x_170 = lean_ctor_get(x_26, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_171 = x_26;
} else {
 lean_dec_ref(x_26);
 x_171 = lean_box(0);
}
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_22);
if (lean_is_scalar(x_171)) {
 x_174 = lean_alloc_ctor(0, 1, 0);
} else {
 x_174 = x_171;
 lean_ctor_set_tag(x_174, 0);
}
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_169);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_25);
if (x_176 == 0)
{
return x_25;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_25, 0);
x_178 = lean_ctor_get(x_25, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_25);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
block_21:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_ctor_set_tag(x_12, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_13);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__0___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__1___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__2___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_9 = 0;
lean_inc_ref(x_4);
x_10 = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(x_9, x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_Split_getSimpMatchContext___redArg(x_4, x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0;
x_17 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1;
x_18 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2;
x_19 = l_Lean_Meta_Split_simpMatch___closed__8;
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed), 11, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_2);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_17);
lean_ctor_set(x_22, 3, x_18);
lean_ctor_set(x_22, 4, x_11);
lean_ctor_set_uint8(x_22, sizeof(void*)*5, x_21);
x_23 = l_Lean_Meta_Simp_main(x_3, x_14, x_19, x_22, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_10, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_19);
lean_dec(x_16);
x_20 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_19, x_4, x_5, x_6, x_7, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec_ref(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = l_Lean_MVarId_replaceTargetEq(x_1, x_22, x_23, x_4, x_5, x_6, x_7, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
return x_9;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_26; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_26 = lean_infer_type(x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_Expr_isEq(x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_30 = l_Lean_Meta_mkHEqRefl(x_7, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_14 = x_31;
x_15 = x_9;
x_16 = x_10;
x_17 = x_11;
x_18 = x_12;
x_19 = x_32;
goto block_25;
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_37 = l_Lean_Meta_mkEqRefl(x_7, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_14 = x_38;
x_15 = x_9;
x_16 = x_10;
x_17 = x_11;
x_18 = x_12;
x_19 = x_39;
goto block_25;
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_40 = !lean_is_exclusive(x_37);
if (x_40 == 0)
{
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
return x_26;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_26);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
block_25:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_1, x_20);
x_22 = lean_array_push(x_2, x_8);
x_23 = lean_array_push(x_3, x_14);
x_24 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg(x_4, x_5, x_6, x_21, x_22, x_23, x_15, x_16, x_17, x_18, x_19);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("heq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_4, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_14 = lean_apply_7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__1;
x_16 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_15, x_10, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_1, x_4);
x_21 = lean_array_get(x_19, x_2, x_4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_20);
x_22 = l_Lean_Meta_mkEqHEq(x_20, x_21, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0___boxed), 13, 7);
lean_closure_set(x_25, 0, x_4);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_6);
lean_closure_set(x_25, 3, x_1);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_3);
lean_closure_set(x_25, 6, x_20);
x_26 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_17, x_23, x_25, x_7, x_8, x_9, x_10, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec_ref(x_20);
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_11 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg(x_1, x_2, x_3, x_9, x_10, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_881_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrGeneralizationFailure", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_881_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_881_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_881_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_881_;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_isDiscrGenException___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Split_discrGenExId;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Split_isDiscrGenException(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Meta_Split_isDiscrGenException___closed__0;
x_6 = lean_nat_dec_eq(x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_isDiscrGenException___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_isDiscrGenException(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_14 = l_Lean_Meta_mkHEqTrans(x_1, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_array_push(x_3, x_8);
x_20 = lean_array_push(x_4, x_15);
x_21 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(x_5, x_6, x_7, x_18, x_19, x_20, x_9, x_10, x_11, x_12, x_16);
return x_21;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_8);
x_14 = l_Lean_Meta_mkEqTrans(x_1, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = lean_array_push(x_3, x_8);
x_20 = lean_array_push(x_4, x_15);
x_21 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(x_5, x_6, x_7, x_18, x_19, x_20, x_9, x_10, x_11, x_12, x_16);
return x_21;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_14;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: encountered unexpected auxiliary equalities created to generalize `match`-expression discriminant\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 239, 239);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_lt(x_4, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_22 = lean_apply_7(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_array_get(x_23, x_1, x_4);
lean_inc_ref(x_7);
x_25 = l_Lean_Meta_getFVarLocalDecl___redArg(x_24, x_7, x_9, x_10, x_11);
lean_dec_ref(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_array_get(x_23, x_3, x_4);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_28);
x_29 = lean_infer_type(x_28, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_50; lean_object* x_51; lean_object* x_64; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_28);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0___boxed), 13, 7);
lean_closure_set(x_32, 0, x_28);
lean_closure_set(x_32, 1, x_4);
lean_closure_set(x_32, 2, x_5);
lean_closure_set(x_32, 3, x_6);
lean_closure_set(x_32, 4, x_1);
lean_closure_set(x_32, 5, x_2);
lean_closure_set(x_32, 6, x_3);
x_50 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1___boxed), 13, 7);
lean_closure_set(x_50, 0, x_28);
lean_closure_set(x_50, 1, x_4);
lean_closure_set(x_50, 2, x_5);
lean_closure_set(x_50, 3, x_6);
lean_closure_set(x_50, 4, x_1);
lean_closure_set(x_50, 5, x_2);
lean_closure_set(x_50, 6, x_3);
x_64 = lean_ctor_get(x_26, 3);
lean_inc_ref(x_64);
x_51 = x_64;
goto block_63;
block_49:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3;
x_39 = lean_unsigned_to_nat(4u);
x_40 = l_Lean_Expr_isAppOfArity(x_30, x_38, x_39);
if (x_40 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_26);
x_12 = x_34;
x_13 = x_35;
x_14 = x_36;
x_15 = x_37;
x_16 = x_31;
goto block_19;
}
else
{
uint8_t x_41; 
x_41 = l_Lean_Expr_isAppOfArity(x_33, x_38, x_39);
if (x_41 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec(x_26);
x_12 = x_34;
x_13 = x_35;
x_14 = x_36;
x_15 = x_37;
x_16 = x_31;
goto block_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_Expr_appArg_x21(x_30);
lean_dec(x_30);
x_43 = l_Lean_Expr_appArg_x21(x_33);
lean_dec_ref(x_33);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
x_44 = l_Lean_Meta_mkHEq(x_42, x_43, x_34, x_35, x_36, x_37, x_31);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec_ref(x_44);
x_47 = lean_ctor_get(x_26, 2);
lean_inc(x_47);
lean_dec(x_26);
x_48 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_47, x_45, x_32, x_34, x_35, x_36, x_37, x_46);
return x_48;
}
else
{
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_26);
return x_44;
}
}
}
}
block_63:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5;
x_53 = lean_unsigned_to_nat(3u);
x_54 = l_Lean_Expr_isAppOfArity(x_30, x_52, x_53);
if (x_54 == 0)
{
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
goto block_49;
}
else
{
uint8_t x_55; 
x_55 = l_Lean_Expr_isAppOfArity(x_51, x_52, x_53);
if (x_55 == 0)
{
lean_dec_ref(x_50);
x_33 = x_51;
x_34 = x_7;
x_35 = x_8;
x_36 = x_9;
x_37 = x_10;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_32);
x_56 = l_Lean_Expr_appArg_x21(x_30);
lean_dec(x_30);
x_57 = l_Lean_Expr_appArg_x21(x_51);
lean_dec_ref(x_51);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_58 = l_Lean_Meta_mkEq(x_56, x_57, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_26, 2);
lean_inc(x_61);
lean_dec(x_26);
x_62 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_61, x_59, x_50, x_7, x_8, x_9, x_10, x_60);
return x_62;
}
else
{
lean_dec_ref(x_50);
lean_dec(x_26);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_58;
}
}
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_29;
}
}
else
{
uint8_t x_65; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_25);
if (x_65 == 0)
{
return x_25;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_25, 0);
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_25);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1;
x_18 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_17, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_array_push(x_4, x_13);
x_5 = x_14;
goto block_9;
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_5 = lean_nat_dec_lt(x_2, x_3);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_of_nat(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0_spec__0(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 4);
x_11 = l_Array_zip___redArg(x_2, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0(x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_11);
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_16 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go(x_3, x_4, x_14, x_12, x_15, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEIO(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__0;
x_8 = l_ReaderT_instMonad___redArg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 4);
x_17 = lean_ctor_get(x_10, 1);
lean_dec(x_17);
x_18 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1;
x_19 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2;
lean_inc_ref(x_13);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_16);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_15);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_25, 0, x_14);
lean_ctor_set(x_10, 4, x_23);
lean_ctor_set(x_10, 3, x_24);
lean_ctor_set(x_10, 2, x_25);
lean_ctor_set(x_10, 1, x_18);
lean_ctor_set(x_10, 0, x_22);
lean_ctor_set(x_8, 1, x_19);
x_26 = l_ReaderT_instMonad___redArg(x_8);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 2);
x_33 = lean_ctor_get(x_28, 3);
x_34 = lean_ctor_get(x_28, 4);
x_35 = lean_ctor_get(x_28, 1);
lean_dec(x_35);
x_36 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
x_37 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
lean_inc_ref(x_31);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_38, 0, x_31);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_41, 0, x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_33);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_43, 0, x_32);
lean_ctor_set(x_28, 4, x_41);
lean_ctor_set(x_28, 3, x_42);
lean_ctor_set(x_28, 2, x_43);
lean_ctor_set(x_28, 1, x_36);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_26, 1, x_37);
x_44 = lean_box(0);
x_45 = l_instInhabitedOfMonad___redArg(x_26, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_5(x_46, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_48 = lean_ctor_get(x_28, 0);
x_49 = lean_ctor_get(x_28, 2);
x_50 = lean_ctor_get(x_28, 3);
x_51 = lean_ctor_get(x_28, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_28);
x_52 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
x_53 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
lean_inc_ref(x_48);
x_54 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_54, 0, x_48);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_55, 0, x_48);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_57, 0, x_51);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_58, 0, x_50);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_59, 0, x_49);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_59);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_57);
lean_ctor_set(x_26, 1, x_53);
lean_ctor_set(x_26, 0, x_60);
x_61 = lean_box(0);
x_62 = l_instInhabitedOfMonad___redArg(x_26, x_61);
x_63 = lean_panic_fn(x_62, x_1);
x_64 = lean_apply_5(x_63, x_2, x_3, x_4, x_5, x_6);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_65 = lean_ctor_get(x_26, 0);
lean_inc(x_65);
lean_dec(x_26);
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 4);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
x_71 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
x_72 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
lean_inc_ref(x_66);
x_73 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_73, 0, x_66);
x_74 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_74, 0, x_66);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_76, 0, x_69);
x_77 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_77, 0, x_68);
x_78 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_78, 0, x_67);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 5, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_78);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_72);
x_81 = lean_box(0);
x_82 = l_instInhabitedOfMonad___redArg(x_80, x_81);
x_83 = lean_panic_fn(x_82, x_1);
x_84 = lean_apply_5(x_83, x_2, x_3, x_4, x_5, x_6);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 2);
x_87 = lean_ctor_get(x_10, 3);
x_88 = lean_ctor_get(x_10, 4);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_89 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1;
x_90 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2;
lean_inc_ref(x_85);
x_91 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_91, 0, x_85);
x_92 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_92, 0, x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_88);
x_95 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_95, 0, x_87);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_96, 0, x_86);
x_97 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_95);
lean_ctor_set(x_97, 4, x_94);
lean_ctor_set(x_8, 1, x_90);
lean_ctor_set(x_8, 0, x_97);
x_98 = l_ReaderT_instMonad___redArg(x_8);
x_99 = lean_ctor_get(x_98, 0);
lean_inc_ref(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 0);
lean_inc_ref(x_101);
x_102 = lean_ctor_get(x_99, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_99, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_99, 4);
lean_inc(x_104);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 lean_ctor_release(x_99, 3);
 lean_ctor_release(x_99, 4);
 x_105 = x_99;
} else {
 lean_dec_ref(x_99);
 x_105 = lean_box(0);
}
x_106 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
x_107 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
lean_inc_ref(x_101);
x_108 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_108, 0, x_101);
x_109 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_109, 0, x_101);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_111, 0, x_104);
x_112 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_112, 0, x_103);
x_113 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_113, 0, x_102);
if (lean_is_scalar(x_105)) {
 x_114 = lean_alloc_ctor(0, 5, 0);
} else {
 x_114 = x_105;
}
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_106);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_112);
lean_ctor_set(x_114, 4, x_111);
if (lean_is_scalar(x_100)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_100;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_107);
x_116 = lean_box(0);
x_117 = l_instInhabitedOfMonad___redArg(x_115, x_116);
x_118 = lean_panic_fn(x_117, x_1);
x_119 = lean_apply_5(x_118, x_2, x_3, x_4, x_5, x_6);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_120 = lean_ctor_get(x_8, 0);
lean_inc(x_120);
lean_dec(x_8);
x_121 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_121);
x_122 = lean_ctor_get(x_120, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 3);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 4);
lean_inc(x_124);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 lean_ctor_release(x_120, 2);
 lean_ctor_release(x_120, 3);
 lean_ctor_release(x_120, 4);
 x_125 = x_120;
} else {
 lean_dec_ref(x_120);
 x_125 = lean_box(0);
}
x_126 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1;
x_127 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2;
lean_inc_ref(x_121);
x_128 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_128, 0, x_121);
x_129 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_129, 0, x_121);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_131, 0, x_124);
x_132 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_132, 0, x_123);
x_133 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_133, 0, x_122);
if (lean_is_scalar(x_125)) {
 x_134 = lean_alloc_ctor(0, 5, 0);
} else {
 x_134 = x_125;
}
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_132);
lean_ctor_set(x_134, 4, x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_127);
x_136 = l_ReaderT_instMonad___redArg(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_137, 0);
lean_inc_ref(x_139);
x_140 = lean_ctor_get(x_137, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_137, 3);
lean_inc(x_141);
x_142 = lean_ctor_get(x_137, 4);
lean_inc(x_142);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 lean_ctor_release(x_137, 2);
 lean_ctor_release(x_137, 3);
 lean_ctor_release(x_137, 4);
 x_143 = x_137;
} else {
 lean_dec_ref(x_137);
 x_143 = lean_box(0);
}
x_144 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
x_145 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
lean_inc_ref(x_139);
x_146 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_146, 0, x_139);
x_147 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_147, 0, x_139);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_149, 0, x_142);
x_150 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_150, 0, x_141);
x_151 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_151, 0, x_140);
if (lean_is_scalar(x_143)) {
 x_152 = lean_alloc_ctor(0, 5, 0);
} else {
 x_152 = x_143;
}
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_144);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_150);
lean_ctor_set(x_152, 4, x_149);
if (lean_is_scalar(x_138)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_138;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_145);
x_154 = lean_box(0);
x_155 = l_instInhabitedOfMonad___redArg(x_153, x_154);
x_156 = lean_panic_fn(x_155, x_1);
x_157 = lean_apply_5(x_156, x_2, x_3, x_4, x_5, x_6);
return x_157;
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Match.MatcherApp.Basic", 32, 32);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.matchMatcherApp\?", 26, 26);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2;
x_2 = lean_unsigned_to_nat(53u);
x_3 = lean_unsigned_to_nat(63u);
x_4 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__1;
x_5 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec_ref(x_11);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_array_push(x_2, x_15);
x_1 = x_10;
x_2 = x_16;
x_7 = x_14;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec_ref(x_11);
x_19 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0(x_19, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec_ref(x_20);
x_1 = x_10;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 6)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec_ref(x_12);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_array_push(x_3, x_16);
x_18 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg(x_11, x_17, x_4, x_5, x_6, x_7, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec_ref(x_12);
x_20 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_21 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0(x_20, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg(x_11, x_3, x_4, x_5, x_6, x_7, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_9);
x_130 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_9, x_6, x_7);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_133);
x_154 = lean_st_ref_get(x_6, x_132);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec_ref(x_154);
if (x_2 == 0)
{
lean_dec(x_155);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
goto block_219;
}
else
{
lean_object* x_220; uint8_t x_221; 
x_220 = lean_ctor_get(x_155, 0);
lean_inc_ref(x_220);
lean_dec(x_155);
lean_inc(x_9);
x_221 = l_Lean_isCasesOnRecursor(x_220, x_9);
if (x_221 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
goto block_219;
}
else
{
if (lean_obj_tag(x_9) == 0)
{
x_157 = x_9;
goto block_216;
}
else
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_9, 0);
lean_inc(x_222);
x_157 = x_222;
goto block_216;
}
}
}
block_216:
{
lean_object* x_158; 
x_158 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_157, x_3, x_4, x_5, x_6, x_156);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 5)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_160);
lean_dec(x_159);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_162 = lean_ctor_get(x_158, 1);
x_163 = lean_ctor_get(x_158, 0);
lean_dec(x_163);
x_164 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_164);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 4);
lean_inc(x_167);
x_168 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2;
x_169 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_169);
x_170 = lean_mk_array(x_169, x_168);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_sub(x_169, x_171);
lean_dec(x_169);
x_173 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_170, x_172);
x_174 = lean_nat_add(x_165, x_171);
x_175 = lean_nat_add(x_174, x_166);
x_176 = lean_nat_add(x_175, x_171);
lean_dec(x_175);
x_177 = l_Lean_InductiveVal_numCtors(x_160);
lean_dec_ref(x_160);
x_178 = lean_nat_add(x_176, x_177);
lean_dec(x_177);
x_179 = lean_array_get_size(x_173);
x_180 = lean_nat_dec_le(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_174);
lean_dec_ref(x_173);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_181 = lean_box(0);
lean_ctor_set(x_158, 0, x_181);
return x_158;
}
else
{
lean_object* x_182; uint8_t x_183; 
lean_free_object(x_158);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_nat_dec_le(x_165, x_179);
if (x_183 == 0)
{
lean_inc(x_179);
x_135 = x_179;
x_136 = x_178;
x_137 = x_162;
x_138 = x_174;
x_139 = x_166;
x_140 = x_180;
x_141 = x_167;
x_142 = x_165;
x_143 = x_173;
x_144 = x_171;
x_145 = x_164;
x_146 = x_176;
x_147 = x_182;
x_148 = x_179;
goto block_153;
}
else
{
lean_inc(x_165);
x_135 = x_179;
x_136 = x_178;
x_137 = x_162;
x_138 = x_174;
x_139 = x_166;
x_140 = x_180;
x_141 = x_167;
x_142 = x_165;
x_143 = x_173;
x_144 = x_171;
x_145 = x_164;
x_146 = x_176;
x_147 = x_182;
x_148 = x_165;
goto block_153;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_184 = lean_ctor_get(x_158, 1);
lean_inc(x_184);
lean_dec(x_158);
x_185 = lean_ctor_get(x_160, 0);
lean_inc_ref(x_185);
x_186 = lean_ctor_get(x_160, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_160, 2);
lean_inc(x_187);
x_188 = lean_ctor_get(x_160, 4);
lean_inc(x_188);
x_189 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2;
x_190 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_190);
x_191 = lean_mk_array(x_190, x_189);
x_192 = lean_unsigned_to_nat(1u);
x_193 = lean_nat_sub(x_190, x_192);
lean_dec(x_190);
x_194 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_191, x_193);
x_195 = lean_nat_add(x_186, x_192);
x_196 = lean_nat_add(x_195, x_187);
x_197 = lean_nat_add(x_196, x_192);
lean_dec(x_196);
x_198 = l_Lean_InductiveVal_numCtors(x_160);
lean_dec_ref(x_160);
x_199 = lean_nat_add(x_197, x_198);
lean_dec(x_198);
x_200 = lean_array_get_size(x_194);
x_201 = lean_nat_dec_le(x_199, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_194);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec_ref(x_185);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_184);
return x_203;
}
else
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_unsigned_to_nat(0u);
x_205 = lean_nat_dec_le(x_186, x_200);
if (x_205 == 0)
{
lean_inc(x_200);
x_135 = x_200;
x_136 = x_199;
x_137 = x_184;
x_138 = x_195;
x_139 = x_187;
x_140 = x_201;
x_141 = x_188;
x_142 = x_186;
x_143 = x_194;
x_144 = x_192;
x_145 = x_185;
x_146 = x_197;
x_147 = x_204;
x_148 = x_200;
goto block_153;
}
else
{
lean_inc(x_186);
x_135 = x_200;
x_136 = x_199;
x_137 = x_184;
x_138 = x_195;
x_139 = x_187;
x_140 = x_201;
x_141 = x_188;
x_142 = x_186;
x_143 = x_194;
x_144 = x_192;
x_145 = x_185;
x_146 = x_197;
x_147 = x_204;
x_148 = x_186;
goto block_153;
}
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_159);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_206 = !lean_is_exclusive(x_158);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_158, 0);
lean_dec(x_207);
x_208 = lean_box(0);
lean_ctor_set(x_158, 0, x_208);
return x_158;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_158, 1);
lean_inc(x_209);
lean_dec(x_158);
x_210 = lean_box(0);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_212 = !lean_is_exclusive(x_158);
if (x_212 == 0)
{
return x_158;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_158, 0);
x_214 = lean_ctor_get(x_158, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_158);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
block_219:
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_box(0);
x_218 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(x_217, x_3, x_4, x_5, x_6, x_156);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_218;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_223 = lean_ctor_get(x_131, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_224 = x_131;
} else {
 lean_dec_ref(x_131);
 x_224 = lean_box(0);
}
x_225 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2;
x_226 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_226);
x_227 = lean_mk_array(x_226, x_225);
x_228 = lean_unsigned_to_nat(1u);
x_229 = lean_nat_sub(x_226, x_228);
lean_dec(x_226);
x_230 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_227, x_229);
x_231 = lean_array_get_size(x_230);
x_232 = l_Lean_Meta_Match_MatcherInfo_arity(x_223);
x_233 = lean_nat_dec_lt(x_231, x_232);
lean_dec(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_275; uint8_t x_278; 
x_234 = lean_ctor_get(x_223, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_223, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_223, 2);
lean_inc_ref(x_236);
x_237 = lean_ctor_get(x_223, 3);
lean_inc(x_237);
x_238 = lean_ctor_get(x_223, 4);
lean_inc_ref(x_238);
x_239 = lean_array_mk(x_10);
x_240 = lean_unsigned_to_nat(0u);
lean_inc(x_234);
x_241 = l_Array_extract___redArg(x_230, x_240, x_234);
x_242 = lean_array_get(x_134, x_230, x_234);
x_265 = lean_nat_add(x_234, x_228);
lean_dec(x_234);
x_266 = lean_nat_add(x_265, x_235);
lean_dec(x_235);
x_278 = lean_nat_dec_le(x_265, x_240);
if (x_278 == 0)
{
x_275 = x_265;
goto block_277;
}
else
{
lean_dec(x_265);
x_275 = x_240;
goto block_277;
}
block_251:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_246 = l_Array_toSubarray___redArg(x_230, x_245, x_231);
x_247 = l_Array_ofSubarray___redArg(x_246);
x_248 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_248, 0, x_9);
lean_ctor_set(x_248, 1, x_239);
lean_ctor_set(x_248, 2, x_237);
lean_ctor_set(x_248, 3, x_238);
lean_ctor_set(x_248, 4, x_241);
lean_ctor_set(x_248, 5, x_242);
lean_ctor_set(x_248, 6, x_244);
lean_ctor_set(x_248, 7, x_236);
lean_ctor_set(x_248, 8, x_243);
lean_ctor_set(x_248, 9, x_247);
if (lean_is_scalar(x_224)) {
 x_249 = lean_alloc_ctor(1, 1, 0);
} else {
 x_249 = x_224;
}
lean_ctor_set(x_249, 0, x_248);
if (lean_is_scalar(x_133)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_133;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_132);
return x_250;
}
block_259:
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_inc_ref(x_230);
x_256 = l_Array_toSubarray___redArg(x_230, x_254, x_255);
x_257 = l_Array_ofSubarray___redArg(x_256);
x_258 = lean_nat_dec_le(x_253, x_240);
if (x_258 == 0)
{
x_243 = x_257;
x_244 = x_252;
x_245 = x_253;
goto block_251;
}
else
{
lean_dec(x_253);
x_243 = x_257;
x_244 = x_252;
x_245 = x_240;
goto block_251;
}
}
block_264:
{
uint8_t x_263; 
x_263 = lean_nat_dec_le(x_261, x_231);
if (x_263 == 0)
{
lean_inc(x_231);
x_252 = x_260;
x_253 = x_261;
x_254 = x_262;
x_255 = x_231;
goto block_259;
}
else
{
lean_inc(x_261);
x_252 = x_260;
x_253 = x_261;
x_254 = x_262;
x_255 = x_261;
goto block_259;
}
}
block_274:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
lean_inc_ref(x_230);
x_269 = l_Array_toSubarray___redArg(x_230, x_267, x_268);
x_270 = l_Array_ofSubarray___redArg(x_269);
x_271 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_223);
lean_dec(x_223);
x_272 = lean_nat_add(x_266, x_271);
lean_dec(x_271);
x_273 = lean_nat_dec_le(x_266, x_240);
if (x_273 == 0)
{
x_260 = x_270;
x_261 = x_272;
x_262 = x_266;
goto block_264;
}
else
{
lean_dec(x_266);
x_260 = x_270;
x_261 = x_272;
x_262 = x_240;
goto block_264;
}
}
block_277:
{
uint8_t x_276; 
x_276 = lean_nat_dec_le(x_266, x_231);
if (x_276 == 0)
{
lean_inc(x_231);
x_267 = x_275;
x_268 = x_231;
goto block_274;
}
else
{
lean_inc(x_266);
x_267 = x_275;
x_268 = x_266;
goto block_274;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_10);
lean_dec(x_9);
x_279 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_133;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_132);
return x_280;
}
}
block_45:
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
lean_inc(x_15);
x_21 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(x_15, x_15, x_20, x_3, x_4, x_5, x_6, x_13);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_array_mk(x_10);
x_25 = l_Array_ofSubarray___redArg(x_18);
x_26 = l_Array_ofSubarray___redArg(x_16);
x_27 = l_Array_ofSubarray___redArg(x_14);
x_28 = l_Array_ofSubarray___redArg(x_12);
x_29 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_19);
lean_ctor_set(x_29, 3, x_17);
lean_ctor_set(x_29, 4, x_25);
lean_ctor_set(x_29, 5, x_11);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_23);
lean_ctor_set(x_29, 8, x_27);
lean_ctor_set(x_29, 9, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_array_mk(x_10);
x_34 = l_Array_ofSubarray___redArg(x_18);
x_35 = l_Array_ofSubarray___redArg(x_16);
x_36 = l_Array_ofSubarray___redArg(x_14);
x_37 = l_Array_ofSubarray___redArg(x_12);
x_38 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_19);
lean_ctor_set(x_38, 3, x_17);
lean_ctor_set(x_38, 4, x_34);
lean_ctor_set(x_38, 5, x_11);
lean_ctor_set(x_38, 6, x_35);
lean_ctor_set(x_38, 7, x_31);
lean_ctor_set(x_38, 8, x_36);
lean_ctor_set(x_38, 9, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_64:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec_ref(x_52);
x_58 = l_Array_toSubarray___redArg(x_50, x_55, x_56);
x_59 = l_List_lengthTR___redArg(x_57);
lean_dec(x_57);
x_60 = l_List_lengthTR___redArg(x_10);
x_61 = lean_nat_dec_eq(x_59, x_60);
lean_dec(x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1;
x_11 = x_46;
x_12 = x_58;
x_13 = x_47;
x_14 = x_48;
x_15 = x_49;
x_16 = x_51;
x_17 = x_54;
x_18 = x_53;
x_19 = x_62;
goto block_45;
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_11 = x_46;
x_12 = x_58;
x_13 = x_47;
x_14 = x_48;
x_15 = x_49;
x_16 = x_51;
x_17 = x_54;
x_18 = x_53;
x_19 = x_63;
goto block_45;
}
}
block_80:
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_inc_ref(x_70);
x_77 = l_Array_toSubarray___redArg(x_70, x_75, x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_le(x_67, x_78);
if (x_79 == 0)
{
x_46 = x_65;
x_47 = x_68;
x_48 = x_77;
x_49 = x_69;
x_50 = x_70;
x_51 = x_71;
x_52 = x_74;
x_53 = x_73;
x_54 = x_72;
x_55 = x_67;
x_56 = x_66;
goto block_64;
}
else
{
lean_dec(x_67);
x_46 = x_65;
x_47 = x_68;
x_48 = x_77;
x_49 = x_69;
x_50 = x_70;
x_51 = x_71;
x_52 = x_74;
x_53 = x_73;
x_54 = x_72;
x_55 = x_78;
x_56 = x_66;
goto block_64;
}
}
block_93:
{
if (x_85 == 0)
{
lean_inc(x_82);
x_65 = x_81;
x_66 = x_82;
x_67 = x_84;
x_68 = x_83;
x_69 = x_86;
x_70 = x_87;
x_71 = x_88;
x_72 = x_91;
x_73 = x_90;
x_74 = x_89;
x_75 = x_92;
x_76 = x_82;
goto block_80;
}
else
{
lean_inc(x_84);
x_65 = x_81;
x_66 = x_82;
x_67 = x_84;
x_68 = x_83;
x_69 = x_86;
x_70 = x_87;
x_71 = x_88;
x_72 = x_91;
x_73 = x_90;
x_74 = x_89;
x_75 = x_92;
x_76 = x_84;
goto block_80;
}
}
block_114:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_inc_ref(x_101);
x_108 = l_Array_toSubarray___redArg(x_101, x_106, x_107);
x_109 = lean_nat_add(x_99, x_104);
lean_dec(x_99);
x_110 = lean_box(0);
x_111 = lean_mk_array(x_109, x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_nat_dec_le(x_105, x_112);
if (x_113 == 0)
{
x_81 = x_94;
x_82 = x_95;
x_83 = x_96;
x_84 = x_97;
x_85 = x_98;
x_86 = x_100;
x_87 = x_101;
x_88 = x_108;
x_89 = x_102;
x_90 = x_103;
x_91 = x_111;
x_92 = x_105;
goto block_93;
}
else
{
lean_dec(x_105);
x_81 = x_94;
x_82 = x_95;
x_83 = x_96;
x_84 = x_97;
x_85 = x_98;
x_86 = x_100;
x_87 = x_101;
x_88 = x_108;
x_89 = x_102;
x_90 = x_103;
x_91 = x_111;
x_92 = x_112;
goto block_93;
}
}
block_129:
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_126, x_116);
if (x_128 == 0)
{
lean_inc(x_116);
x_94 = x_115;
x_95 = x_116;
x_96 = x_118;
x_97 = x_117;
x_98 = x_120;
x_99 = x_119;
x_100 = x_121;
x_101 = x_122;
x_102 = x_125;
x_103 = x_124;
x_104 = x_123;
x_105 = x_126;
x_106 = x_127;
x_107 = x_116;
goto block_114;
}
else
{
lean_inc(x_126);
x_94 = x_115;
x_95 = x_116;
x_96 = x_118;
x_97 = x_117;
x_98 = x_120;
x_99 = x_119;
x_100 = x_121;
x_101 = x_122;
x_102 = x_125;
x_103 = x_124;
x_104 = x_123;
x_105 = x_126;
x_106 = x_127;
x_107 = x_126;
goto block_114;
}
}
block_153:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_inc_ref(x_143);
x_149 = l_Array_toSubarray___redArg(x_143, x_147, x_148);
x_150 = lean_array_get(x_134, x_143, x_142);
lean_dec(x_142);
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_nat_dec_le(x_138, x_151);
if (x_152 == 0)
{
x_115 = x_150;
x_116 = x_135;
x_117 = x_136;
x_118 = x_137;
x_119 = x_139;
x_120 = x_140;
x_121 = x_141;
x_122 = x_143;
x_123 = x_144;
x_124 = x_149;
x_125 = x_145;
x_126 = x_146;
x_127 = x_138;
goto block_129;
}
else
{
lean_dec(x_138);
x_115 = x_150;
x_116 = x_135;
x_117 = x_136;
x_118 = x_137;
x_119 = x_139;
x_120 = x_140;
x_121 = x_141;
x_122 = x_143;
x_123 = x_144;
x_124 = x_149;
x_125 = x_145;
x_126 = x_146;
x_127 = x_151;
goto block_129;
}
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_281 = lean_box(0);
x_282 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(x_281, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_282;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__2;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discr mismatch ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" != ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_34; 
x_22 = lean_ctor_get(x_13, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_13, 0);
lean_dec(x_24);
x_25 = lean_array_uget(x_2, x_4);
x_26 = lean_array_fget(x_15, x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_16, x_27);
lean_dec(x_16);
lean_ctor_set(x_13, 1, x_28);
x_34 = lean_expr_eqv(x_25, x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_1);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_36 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_35, x_8, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec_ref(x_36);
x_29 = x_39;
goto block_33;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
x_44 = l_Lean_MessageData_ofExpr(x_25);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_44);
lean_ctor_set(x_36, 0, x_43);
x_45 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_MessageData_ofExpr(x_26);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_35, x_50, x_6, x_7, x_8, x_9, x_41);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_29 = x_52;
goto block_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
x_55 = l_Lean_MessageData_ofExpr(x_25);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofExpr(x_26);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_35, x_62, x_6, x_7, x_8, x_9, x_53);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_29 = x_64;
goto block_33;
}
}
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_14);
lean_inc(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_13);
x_66 = 1;
x_67 = lean_usize_add(x_4, x_66);
x_4 = x_67;
x_5 = x_65;
goto _start;
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0;
if (lean_is_scalar(x_14)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_14;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_79; 
lean_dec(x_13);
x_69 = lean_array_uget(x_2, x_4);
x_70 = lean_array_fget(x_15, x_16);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_16, x_71);
lean_dec(x_16);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_15);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_17);
x_79 = lean_expr_eqv(x_69, x_70);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_1);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_81 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_80, x_8, x_10);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec_ref(x_81);
x_74 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
x_88 = l_Lean_MessageData_ofExpr(x_69);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(7, 2, 0);
} else {
 x_89 = x_86;
 lean_ctor_set_tag(x_89, 7);
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_70);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_80, x_95, x_6, x_7, x_8, x_9, x_85);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_74 = x_97;
goto block_78;
}
}
else
{
lean_object* x_98; size_t x_99; size_t x_100; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec(x_14);
lean_inc(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_73);
x_99 = 1;
x_100 = lean_usize_add(x_4, x_99);
x_4 = x_100;
x_5 = x_98;
goto _start;
}
block_78:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0;
if (lean_is_scalar(x_14)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_14;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_14 = x_5;
} else {
 lean_dec_ref(x_5);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
}
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_34; 
x_22 = lean_ctor_get(x_13, 2);
lean_dec(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_13, 0);
lean_dec(x_24);
x_25 = lean_array_uget(x_2, x_4);
x_26 = lean_array_fget(x_15, x_16);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_16, x_27);
lean_dec(x_16);
lean_ctor_set(x_13, 1, x_28);
x_34 = lean_expr_eqv(x_25, x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_1);
x_35 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_36 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_35, x_8, x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec_ref(x_36);
x_29 = x_39;
goto block_33;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_36, 1);
x_42 = lean_ctor_get(x_36, 0);
lean_dec(x_42);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
x_44 = l_Lean_MessageData_ofExpr(x_25);
lean_ctor_set_tag(x_36, 7);
lean_ctor_set(x_36, 1, x_44);
lean_ctor_set(x_36, 0, x_43);
x_45 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_MessageData_ofExpr(x_26);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_35, x_50, x_6, x_7, x_8, x_9, x_41);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_29 = x_52;
goto block_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
lean_dec(x_36);
x_54 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
x_55 = l_Lean_MessageData_ofExpr(x_25);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofExpr(x_26);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_35, x_62, x_6, x_7, x_8, x_9, x_53);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_29 = x_64;
goto block_33;
}
}
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec(x_14);
lean_inc(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_13);
x_66 = 1;
x_67 = lean_usize_add(x_4, x_66);
x_68 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4(x_1, x_2, x_3, x_67, x_65, x_6, x_7, x_8, x_9, x_10);
return x_68;
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0;
if (lean_is_scalar(x_14)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_14;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_13);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_79; 
lean_dec(x_13);
x_69 = lean_array_uget(x_2, x_4);
x_70 = lean_array_fget(x_15, x_16);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_16, x_71);
lean_dec(x_16);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_15);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_17);
x_79 = lean_expr_eqv(x_69, x_70);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_1);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_81 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_80, x_8, x_10);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec_ref(x_81);
x_74 = x_84;
goto block_78;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
x_88 = l_Lean_MessageData_ofExpr(x_69);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(7, 2, 0);
} else {
 x_89 = x_86;
 lean_ctor_set_tag(x_89, 7);
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_70);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_80, x_95, x_6, x_7, x_8, x_9, x_85);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
x_74 = x_97;
goto block_78;
}
}
else
{
lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; 
lean_dec_ref(x_70);
lean_dec_ref(x_69);
lean_dec(x_14);
lean_inc(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_73);
x_99 = 1;
x_100 = lean_usize_add(x_4, x_99);
x_101 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4(x_1, x_2, x_3, x_100, x_98, x_6, x_7, x_8, x_9, x_10);
return x_101;
}
block_78:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0;
if (lean_is_scalar(x_14)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_14;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_replaceFVars(x_1, x_2, x_8);
x_15 = l_Array_ofSubarray___redArg(x_3);
x_16 = l_Array_append___redArg(x_15, x_7);
x_17 = l_Lean_Meta_mkLambdaFVars(x_16, x_14, x_4, x_5, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: encountered an unexpected `match` expression alternative\nthis error typically occurs when the `match` expression has been constructed using meta-programming.", 191, 191);
return x_1;
}
}
static lean_object* _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_86; uint8_t x_94; lean_object* x_102; uint8_t x_103; 
x_102 = lean_array_get_size(x_11);
x_103 = lean_nat_dec_lt(x_102, x_6);
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = lean_nat_dec_lt(x_102, x_3);
lean_dec(x_102);
x_94 = x_104;
goto block_101;
}
else
{
lean_dec(x_102);
x_94 = x_2;
goto block_101;
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Array_toSubarray___redArg(x_11, x_26, x_27);
x_29 = l_Array_ofSubarray___redArg(x_28);
x_30 = lean_box(x_1);
x_31 = lean_box(x_2);
x_32 = lean_box(x_20);
lean_inc_ref(x_29);
x_33 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0___boxed), 13, 6);
lean_closure_set(x_33, 0, x_19);
lean_closure_set(x_33, 1, x_29);
lean_closure_set(x_33, 2, x_18);
lean_closure_set(x_33, 3, x_30);
lean_closure_set(x_33, 4, x_31);
lean_closure_set(x_33, 5, x_32);
x_34 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(x_4, x_5, x_29, x_33, x_21, x_23, x_22, x_24, x_25);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_34;
}
block_47:
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_6, x_41);
if (x_46 == 0)
{
lean_dec(x_6);
x_18 = x_36;
x_19 = x_37;
x_20 = x_38;
x_21 = x_39;
x_22 = x_40;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = x_45;
x_27 = x_41;
goto block_35;
}
else
{
lean_dec(x_41);
x_18 = x_36;
x_19 = x_37;
x_20 = x_38;
x_21 = x_39;
x_22 = x_40;
x_23 = x_42;
x_24 = x_43;
x_25 = x_44;
x_26 = x_45;
x_27 = x_6;
goto block_35;
}
}
block_66:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_inc_ref(x_11);
x_59 = l_Array_toSubarray___redArg(x_11, x_57, x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_3, x_60);
lean_dec(x_3);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_array_get_size(x_11);
x_63 = lean_nat_dec_le(x_54, x_60);
if (x_63 == 0)
{
x_36 = x_59;
x_37 = x_49;
x_38 = x_50;
x_39 = x_52;
x_40 = x_53;
x_41 = x_62;
x_42 = x_55;
x_43 = x_56;
x_44 = x_48;
x_45 = x_54;
goto block_47;
}
else
{
lean_dec(x_54);
x_36 = x_59;
x_37 = x_49;
x_38 = x_50;
x_39 = x_52;
x_40 = x_53;
x_41 = x_62;
x_42 = x_55;
x_43 = x_56;
x_44 = x_48;
x_45 = x_60;
goto block_47;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_54);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_64 = l_Array_ofSubarray___redArg(x_59);
x_65 = l_Lean_Meta_mkLambdaFVars(x_64, x_49, x_1, x_2, x_1, x_2, x_51, x_52, x_55, x_53, x_56, x_48);
lean_dec(x_56);
lean_dec_ref(x_53);
lean_dec(x_55);
lean_dec_ref(x_52);
return x_65;
}
}
block_85:
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
lean_inc_ref(x_11);
x_75 = l_Array_toSubarray___redArg(x_11, x_73, x_74);
x_76 = l_Array_ofSubarray___redArg(x_75);
x_77 = 1;
x_78 = l_Lean_Meta_mkLambdaFVars(x_76, x_70, x_1, x_2, x_1, x_2, x_77, x_68, x_71, x_69, x_72, x_67);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
x_81 = lean_nat_sub(x_6, x_3);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get_size(x_11);
x_84 = lean_nat_dec_le(x_81, x_83);
if (x_84 == 0)
{
x_48 = x_80;
x_49 = x_79;
x_50 = x_77;
x_51 = x_77;
x_52 = x_68;
x_53 = x_69;
x_54 = x_81;
x_55 = x_71;
x_56 = x_72;
x_57 = x_82;
x_58 = x_83;
goto block_66;
}
else
{
lean_dec(x_83);
lean_inc(x_81);
x_48 = x_80;
x_49 = x_79;
x_50 = x_77;
x_51 = x_77;
x_52 = x_68;
x_53 = x_69;
x_54 = x_81;
x_55 = x_71;
x_56 = x_72;
x_57 = x_82;
x_58 = x_81;
goto block_66;
}
}
else
{
lean_dec(x_72);
lean_dec(x_71);
lean_dec_ref(x_69);
lean_dec_ref(x_68);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_78;
}
}
block_93:
{
lean_object* x_87; 
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc_ref(x_5);
lean_inc(x_3);
lean_inc_ref(x_4);
x_87 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(x_7, x_8, x_4, x_3, x_9, x_5, x_10, x_12, x_13, x_14, x_15, x_16, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec_ref(x_87);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_array_get_size(x_11);
x_92 = lean_nat_dec_le(x_6, x_90);
if (x_92 == 0)
{
lean_inc(x_6);
x_67 = x_89;
x_68 = x_13;
x_69 = x_15;
x_70 = x_88;
x_71 = x_14;
x_72 = x_16;
x_73 = x_6;
x_74 = x_91;
goto block_85;
}
else
{
x_67 = x_89;
x_68 = x_13;
x_69 = x_15;
x_70 = x_88;
x_71 = x_14;
x_72 = x_16;
x_73 = x_90;
x_74 = x_91;
goto block_85;
}
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_11);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_87;
}
}
block_101:
{
if (x_94 == 0)
{
x_86 = x_17;
goto block_93;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_95 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1;
x_96 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_95, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_array_fget(x_1, x_15);
lean_inc(x_2);
x_22 = lean_array_get(x_2, x_3, x_15);
x_23 = lean_box(x_11);
x_24 = lean_box(x_12);
lean_inc(x_10);
lean_inc_ref(x_8);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_7);
x_25 = lean_alloc_closure((void*)(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(x_25, 0, x_23);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_7);
lean_closure_set(x_25, 3, x_6);
lean_closure_set(x_25, 4, x_9);
lean_closure_set(x_25, 5, x_22);
lean_closure_set(x_25, 6, x_4);
lean_closure_set(x_25, 7, x_5);
lean_closure_set(x_25, 8, x_8);
lean_closure_set(x_25, 9, x_10);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
x_26 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_21, x_25, x_11, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_array_push(x_14, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_15, x_31);
lean_dec(x_15);
x_33 = lean_nat_dec_lt(x_32, x_13);
if (x_33 == 0)
{
lean_dec(x_32);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_free_object(x_26);
x_14 = x_30;
x_15 = x_32;
x_20 = x_29;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_array_push(x_14, x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_15, x_38);
lean_dec(x_15);
x_40 = lean_nat_dec_lt(x_39, x_13);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_39);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
x_14 = x_37;
x_15 = x_39;
x_20 = x_36;
goto _start;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_26);
if (x_43 == 0)
{
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26, lean_object* x_27) {
_start:
{
lean_object* x_28; 
x_28 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17, x_19, x_20, x_23, x_24, x_25, x_26, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Meta_Match_MatcherInfo_arity(x_1);
x_16 = l_Lean_Expr_isAppOfArity(x_9, x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; 
x_19 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
x_20 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(x_9, x_19, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_29 = x_21;
} else {
 lean_dec_ref(x_21);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_31 = x_20;
} else {
 lean_dec_ref(x_20);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_28, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 3);
lean_inc_ref(x_35);
x_36 = lean_ctor_get(x_28, 4);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_28, 5);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_28, 6);
lean_inc_ref(x_38);
x_39 = lean_ctor_get(x_28, 7);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_28, 8);
lean_inc_ref(x_40);
x_41 = lean_ctor_get(x_28, 9);
lean_inc_ref(x_41);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 lean_ctor_release(x_28, 2);
 lean_ctor_release(x_28, 3);
 lean_ctor_release(x_28, 4);
 lean_ctor_release(x_28, 5);
 lean_ctor_release(x_28, 6);
 lean_ctor_release(x_28, 7);
 lean_ctor_release(x_28, 8);
 lean_ctor_release(x_28, 9);
 x_42 = x_28;
} else {
 lean_dec_ref(x_28);
 x_42 = lean_box(0);
}
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get_size(x_3);
lean_inc_ref(x_3);
x_52 = l_Array_toSubarray___redArg(x_3, x_50, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = lean_array_size(x_38);
x_56 = 0;
x_57 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(x_53, x_38, x_55, x_56, x_54, x_10, x_11, x_12, x_13, x_30);
lean_dec_ref(x_38);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec_ref(x_57);
x_61 = lean_box(x_16);
x_62 = lean_st_ref_set(x_4, x_61, x_60);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_array_get_size(x_40);
x_65 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_66 = lean_nat_dec_lt(x_50, x_64);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec_ref(x_40);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = x_65;
x_44 = x_63;
goto block_49;
}
else
{
lean_object* x_67; 
lean_inc_ref(x_5);
x_67 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_40, x_6, x_39, x_2, x_3, x_1, x_7, x_5, x_8, x_4, x_19, x_16, x_64, x_65, x_50, x_10, x_11, x_12, x_13, x_63);
lean_dec(x_64);
lean_dec_ref(x_40);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec_ref(x_67);
x_43 = x_68;
x_44 = x_69;
goto block_49;
}
else
{
uint8_t x_70; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_39);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec_ref(x_5);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_57);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_57, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_76);
return x_57;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_57, 1);
lean_inc(x_77);
lean_dec(x_57);
x_78 = lean_ctor_get(x_59, 0);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
block_49:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 10, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set(x_45, 4, x_36);
lean_ctor_set(x_45, 5, x_37);
lean_ctor_set(x_45, 6, x_5);
lean_ctor_set(x_45, 7, x_39);
lean_ctor_set(x_45, 8, x_43);
lean_ctor_set(x_45, 9, x_41);
x_46 = l_Lean_Meta_MatcherApp_toExpr(x_45);
if (lean_is_scalar(x_29)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_29;
 lean_ctor_set_tag(x_47, 0);
}
lean_ctor_set(x_47, 0, x_46);
if (lean_is_scalar(x_31)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_31;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_20);
if (x_80 == 0)
{
return x_20;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_20, 0);
x_82 = lean_ctor_get(x_20, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_20);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_8, x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0___boxed), 6, 0);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__1), 14, 8);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_7);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_18);
lean_closure_set(x_19, 6, x_4);
lean_closure_set(x_19, 7, x_6);
x_20 = 0;
x_21 = l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(x_15, x_19, x_17, x_20, x_20, x_9, x_10, x_11, x_12, x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_4);
x_15 = lean_unbox(x_5);
x_16 = lean_unbox(x_6);
x_17 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0(x_1, x_2, x_3, x_14, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___boxed(lean_object** _args) {
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
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_1);
x_19 = lean_unbox(x_2);
x_20 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1(x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_11);
x_22 = lean_unbox(x_12);
x_23 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_22, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
lean_object* x_27 = _args[26];
_start:
{
uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_unbox(x_11);
x_29 = lean_unbox(x_12);
x_30 = lean_unbox(x_13);
x_31 = l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_28, x_29, x_30, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_18);
lean_dec(x_17);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: failed to find match-expression discriminants\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 187, 187);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Split_isDiscrGenException___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_box(x_1);
x_16 = lean_st_mk_ref(x_15, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = l_Lean_MVarId_getType(x_2, x_10, x_11, x_12, x_13, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_17);
lean_inc_ref(x_8);
lean_inc_ref(x_7);
x_22 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_20, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_st_ref_get(x_17, x_24);
lean_dec(x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec_ref(x_25);
x_29 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1;
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_25, 1);
x_37 = lean_ctor_get(x_25, 0);
lean_dec(x_37);
x_38 = l_Array_append___redArg(x_7, x_8);
lean_dec_ref(x_8);
x_39 = 1;
x_40 = lean_unbox(x_26);
x_41 = lean_unbox(x_26);
lean_dec(x_26);
x_42 = l_Lean_Meta_mkForallFVars(x_38, x_23, x_1, x_40, x_41, x_39, x_10, x_11, x_12, x_13, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
lean_inc(x_43);
x_45 = l_Lean_Meta_isTypeCorrect(x_43, x_10, x_11, x_12, x_13, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_43);
lean_free_object(x_25);
lean_dec_ref(x_9);
x_48 = !lean_is_exclusive(x_45);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_dec(x_49);
x_50 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_50);
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
x_52 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_45, 0);
lean_dec(x_55);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 0, x_43);
lean_ctor_set(x_45, 0, x_25);
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_dec(x_45);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 0, x_43);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_25);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_43);
lean_free_object(x_25);
lean_dec_ref(x_9);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_free_object(x_25);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_62 = !lean_is_exclusive(x_42);
if (x_62 == 0)
{
return x_42;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_42, 0);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_42);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_25, 1);
lean_inc(x_66);
lean_dec(x_25);
x_67 = l_Array_append___redArg(x_7, x_8);
lean_dec_ref(x_8);
x_68 = 1;
x_69 = lean_unbox(x_26);
x_70 = lean_unbox(x_26);
lean_dec(x_26);
x_71 = l_Lean_Meta_mkForallFVars(x_67, x_23, x_1, x_69, x_70, x_68, x_10, x_11, x_12, x_13, x_66);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
lean_inc(x_72);
x_74 = l_Lean_Meta_isTypeCorrect(x_72, x_10, x_11, x_12, x_13, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec_ref(x_9);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_78 = x_74;
} else {
 lean_dec_ref(x_74);
 x_78 = lean_box(0);
}
x_79 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_78;
 lean_ctor_set_tag(x_80, 1);
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_72);
lean_ctor_set(x_83, 1, x_9);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
lean_dec_ref(x_9);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_87 = x_74;
} else {
 lean_dec_ref(x_74);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
x_89 = lean_ctor_get(x_71, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_91 = x_71;
} else {
 lean_dec_ref(x_71);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_93 = !lean_is_exclusive(x_22);
if (x_93 == 0)
{
return x_22;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_22, 0);
x_95 = lean_ctor_get(x_22, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_22);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_19);
if (x_97 == 0)
{
return x_19;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_19, 0);
x_99 = lean_ctor_get(x_19, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_19);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_1);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___boxed), 14, 7);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
lean_closure_set(x_15, 4, x_5);
lean_closure_set(x_15, 5, x_6);
lean_closure_set(x_15, 6, x_7);
x_16 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg(x_4, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.Tactic.Split", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Split.0.Lean.Meta.Split.generalizeMatchDiscrs", 71, 71);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2;
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_unsigned_to_nat(125u);
x_4 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1;
x_5 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("targetNew:\n", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_2, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2;
x_15 = l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0(x_14, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_18);
x_20 = lean_box(x_1);
lean_inc_ref(x_4);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed), 13, 6);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_18);
lean_closure_set(x_21, 5, x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_22 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_5, x_21, x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_3);
x_27 = l_Lean_MVarId_getTag(x_3, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc_ref(x_6);
x_30 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_25, x_28, x_6, x_7, x_8, x_9, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_80 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_81 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_80, x_8, x_33);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_free_object(x_30);
lean_free_object(x_12);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec_ref(x_81);
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_84;
goto block_79;
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_86 = lean_ctor_get(x_81, 1);
x_87 = lean_ctor_get(x_81, 0);
lean_dec(x_87);
x_88 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_89 = l_Lean_Expr_mvarId_x21(x_32);
lean_ctor_set(x_12, 0, x_89);
lean_ctor_set_tag(x_81, 7);
lean_ctor_set(x_81, 1, x_12);
lean_ctor_set(x_81, 0, x_88);
x_90 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_90);
lean_ctor_set(x_30, 0, x_81);
x_91 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_80, x_30, x_6, x_7, x_8, x_9, x_86);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec_ref(x_91);
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_92;
goto block_79;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
lean_dec(x_81);
x_94 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_95 = l_Lean_Expr_mvarId_x21(x_32);
lean_ctor_set(x_12, 0, x_95);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_12);
x_97 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_97);
lean_ctor_set(x_30, 0, x_96);
x_98 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_80, x_30, x_6, x_7, x_8, x_9, x_93);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec_ref(x_98);
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_99;
goto block_79;
}
}
block_79:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
lean_inc(x_32);
x_39 = l_Lean_mkAppN(x_32, x_4);
x_40 = l_Lean_mkAppN(x_39, x_26);
lean_dec(x_26);
x_41 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_40, x_35, x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
x_44 = lean_array_get_size(x_4);
lean_dec_ref(x_4);
x_45 = lean_box(0);
x_46 = 1;
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_44);
x_47 = l_Lean_Meta_introNCore(x_43, x_44, x_45, x_1, x_46, x_34, x_35, x_36, x_37, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 1);
x_53 = l_Lean_Meta_introNCore(x_52, x_44, x_45, x_1, x_46, x_34, x_35, x_36, x_37, x_49);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_48, 1, x_55);
lean_ctor_set(x_53, 0, x_48);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_48, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_free_object(x_48);
lean_dec(x_51);
x_59 = !lean_is_exclusive(x_53);
if (x_59 == 0)
{
return x_53;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_53, 0);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_53);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = l_Lean_Meta_introNCore(x_64, x_44, x_45, x_1, x_46, x_34, x_35, x_36, x_37, x_49);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
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
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_100 = lean_ctor_get(x_30, 0);
x_101 = lean_ctor_get(x_30, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_30);
x_136 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_137 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_136, x_8, x_101);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_free_object(x_12);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec_ref(x_137);
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_140;
goto block_135;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_142 = x_137;
} else {
 lean_dec_ref(x_137);
 x_142 = lean_box(0);
}
x_143 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_144 = l_Lean_Expr_mvarId_x21(x_100);
lean_ctor_set(x_12, 0, x_144);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(7, 2, 0);
} else {
 x_145 = x_142;
 lean_ctor_set_tag(x_145, 7);
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_12);
x_146 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_136, x_147, x_6, x_7, x_8, x_9, x_141);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
x_102 = x_6;
x_103 = x_7;
x_104 = x_8;
x_105 = x_9;
x_106 = x_149;
goto block_135;
}
block_135:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
lean_inc(x_100);
x_107 = l_Lean_mkAppN(x_100, x_4);
x_108 = l_Lean_mkAppN(x_107, x_26);
lean_dec(x_26);
x_109 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_108, x_103, x_106);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = l_Lean_Expr_mvarId_x21(x_100);
lean_dec(x_100);
x_112 = lean_array_get_size(x_4);
lean_dec_ref(x_4);
x_113 = lean_box(0);
x_114 = 1;
lean_inc(x_105);
lean_inc_ref(x_104);
lean_inc(x_103);
lean_inc_ref(x_102);
lean_inc(x_112);
x_115 = l_Lean_Meta_introNCore(x_111, x_112, x_113, x_1, x_114, x_102, x_103, x_104, x_105, x_110);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec_ref(x_115);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
x_121 = l_Lean_Meta_introNCore(x_119, x_112, x_113, x_1, x_114, x_102, x_103, x_104, x_105, x_117);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
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
if (lean_is_scalar(x_120)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_120;
}
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_122);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_123);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_120);
lean_dec(x_118);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_112);
lean_dec(x_105);
lean_dec_ref(x_104);
lean_dec(x_103);
lean_dec_ref(x_102);
x_131 = lean_ctor_get(x_115, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_115, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_133 = x_115;
} else {
 lean_dec_ref(x_115);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_150 = !lean_is_exclusive(x_27);
if (x_150 == 0)
{
return x_27;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_27, 0);
x_152 = lean_ctor_get(x_27, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_27);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_free_object(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_154 = !lean_is_exclusive(x_22);
if (x_154 == 0)
{
return x_22;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_22, 0);
x_156 = lean_ctor_get(x_22, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_22);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_12, 0);
lean_inc(x_158);
lean_dec(x_12);
x_159 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_158);
x_160 = lean_box(x_1);
lean_inc_ref(x_4);
lean_inc(x_3);
x_161 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed), 13, 6);
lean_closure_set(x_161, 0, x_160);
lean_closure_set(x_161, 1, x_3);
lean_closure_set(x_161, 2, x_2);
lean_closure_set(x_161, 3, x_4);
lean_closure_set(x_161, 4, x_158);
lean_closure_set(x_161, 5, x_159);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_162 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_5, x_161, x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec_ref(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
lean_inc(x_3);
x_167 = l_Lean_MVarId_getTag(x_3, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec_ref(x_167);
lean_inc_ref(x_6);
x_170 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_165, x_168, x_6, x_7, x_8, x_9, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_208 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_209 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_208, x_8, x_172);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_unbox(x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; 
lean_dec(x_173);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec_ref(x_209);
x_174 = x_6;
x_175 = x_7;
x_176 = x_8;
x_177 = x_9;
x_178 = x_212;
goto block_207;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_213 = lean_ctor_get(x_209, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_214 = x_209;
} else {
 lean_dec_ref(x_209);
 x_214 = lean_box(0);
}
x_215 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_216 = l_Lean_Expr_mvarId_x21(x_171);
x_217 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_217, 0, x_216);
if (lean_is_scalar(x_214)) {
 x_218 = lean_alloc_ctor(7, 2, 0);
} else {
 x_218 = x_214;
 lean_ctor_set_tag(x_218, 7);
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
if (lean_is_scalar(x_173)) {
 x_220 = lean_alloc_ctor(7, 2, 0);
} else {
 x_220 = x_173;
 lean_ctor_set_tag(x_220, 7);
}
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_208, x_220, x_6, x_7, x_8, x_9, x_213);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec_ref(x_221);
x_174 = x_6;
x_175 = x_7;
x_176 = x_8;
x_177 = x_9;
x_178 = x_222;
goto block_207;
}
block_207:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; lean_object* x_187; 
lean_inc(x_171);
x_179 = l_Lean_mkAppN(x_171, x_4);
x_180 = l_Lean_mkAppN(x_179, x_166);
lean_dec(x_166);
x_181 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_180, x_175, x_178);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec_ref(x_181);
x_183 = l_Lean_Expr_mvarId_x21(x_171);
lean_dec(x_171);
x_184 = lean_array_get_size(x_4);
lean_dec_ref(x_4);
x_185 = lean_box(0);
x_186 = 1;
lean_inc(x_177);
lean_inc_ref(x_176);
lean_inc(x_175);
lean_inc_ref(x_174);
lean_inc(x_184);
x_187 = l_Lean_Meta_introNCore(x_183, x_184, x_185, x_1, x_186, x_174, x_175, x_176, x_177, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec_ref(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = l_Lean_Meta_introNCore(x_191, x_184, x_185, x_1, x_186, x_174, x_175, x_176, x_177, x_189);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_196 = x_193;
} else {
 lean_dec_ref(x_193);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_192;
}
lean_ctor_set(x_197, 0, x_190);
lean_ctor_set(x_197, 1, x_194);
if (lean_is_scalar(x_196)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_196;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_195);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_192);
lean_dec(x_190);
x_199 = lean_ctor_get(x_193, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_201 = x_193;
} else {
 lean_dec_ref(x_193);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_184);
lean_dec(x_177);
lean_dec_ref(x_176);
lean_dec(x_175);
lean_dec_ref(x_174);
x_203 = lean_ctor_get(x_187, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_187, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_205 = x_187;
} else {
 lean_dec_ref(x_187);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_223 = lean_ctor_get(x_167, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_167, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_225 = x_167;
} else {
 lean_dec_ref(x_167);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_227 = lean_ctor_get(x_162, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_162, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_229 = x_162;
} else {
 lean_dec_ref(x_162);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
}
else
{
size_t x_231; size_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_231 = lean_array_size(x_4);
x_232 = 0;
x_233 = l_Array_mapMUnsafe_map___at___Lean_Meta_introNCore_spec__4(x_231, x_232, x_4);
x_234 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5;
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_3);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_10);
return x_237;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_4);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
goto block_16;
}
else
{
if (x_19 == 0)
{
lean_dec(x_18);
goto block_16;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_22 = l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_delabDelayedAssignedMVar_spec__1(x_4, x_20, x_21);
if (x_22 == 0)
{
goto block_16;
}
else
{
uint8_t x_23; 
x_23 = 0;
x_10 = x_23;
goto block_14;
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(x_10);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___boxed), 10, 5);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_3);
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
block_16:
{
uint8_t x_15; 
x_15 = 1;
x_10 = x_15;
goto block_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
x_16 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
x_12 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_3, x_2);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
x_26 = lean_array_uget(x_1, x_3);
x_27 = l_Lean_Expr_fvar___override(x_26);
lean_inc(x_24);
x_28 = l_Lean_Meta_FVarSubst_apply(x_24, x_27);
lean_dec_ref(x_27);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_30 = l_Lean_Meta_heqToEq(x_25, x_29, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_24);
lean_inc(x_33);
lean_inc(x_34);
x_36 = l_Lean_Meta_substCore_x3f(x_34, x_33, x_35, x_24, x_21, x_35, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_24);
lean_inc(x_34);
x_39 = l_Lean_Meta_substCore_x3f(x_34, x_33, x_21, x_24, x_21, x_35, x_5, x_6, x_7, x_8, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_ctor_set(x_4, 1, x_34);
x_10 = x_4;
x_11 = x_41;
goto block_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_24);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec_ref(x_39);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_16 = x_44;
x_17 = x_45;
x_18 = x_43;
goto block_20;
}
}
else
{
uint8_t x_46; 
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_4);
lean_dec(x_24);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
lean_dec(x_37);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_dec_ref(x_36);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_16 = x_52;
x_17 = x_53;
x_18 = x_51;
goto block_20;
}
}
else
{
uint8_t x_54; 
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_54 = !lean_is_exclusive(x_36);
if (x_54 == 0)
{
return x_36;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_36, 0);
x_56 = lean_ctor_get(x_36, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_36);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_58 = !lean_is_exclusive(x_30);
if (x_58 == 0)
{
return x_30;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_30);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_dec_ref(x_28);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_4, 0);
x_63 = lean_ctor_get(x_4, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_4);
x_64 = lean_array_uget(x_1, x_3);
x_65 = l_Lean_Expr_fvar___override(x_64);
lean_inc(x_62);
x_66 = l_Lean_Meta_FVarSubst_apply(x_62, x_65);
lean_dec_ref(x_65);
if (lean_obj_tag(x_66) == 1)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_68 = l_Lean_Meta_heqToEq(x_63, x_67, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_62);
lean_inc(x_71);
lean_inc(x_72);
x_74 = l_Lean_Meta_substCore_x3f(x_72, x_71, x_73, x_62, x_21, x_73, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_62);
lean_inc(x_72);
x_77 = l_Lean_Meta_substCore_x3f(x_72, x_71, x_21, x_62, x_21, x_73, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_62);
lean_ctor_set(x_80, 1, x_72);
x_10 = x_80;
x_11 = x_79;
goto block_15;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_72);
lean_dec(x_62);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec_ref(x_77);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_16 = x_83;
x_17 = x_84;
x_18 = x_82;
goto block_20;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_72);
lean_dec(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_87 = x_77;
} else {
 lean_dec_ref(x_77);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_62);
x_89 = lean_ctor_get(x_75, 0);
lean_inc(x_89);
lean_dec(x_75);
x_90 = lean_ctor_get(x_74, 1);
lean_inc(x_90);
lean_dec_ref(x_74);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_dec(x_89);
x_16 = x_91;
x_17 = x_92;
x_18 = x_90;
goto block_20;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
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
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_62);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_97 = lean_ctor_get(x_68, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_68, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_99 = x_68;
} else {
 lean_dec_ref(x_68);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec_ref(x_66);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_62);
lean_ctor_set(x_101, 1, x_63);
x_10 = x_101;
x_11 = x_9;
goto block_15;
}
}
}
block_15:
{
size_t x_12; size_t x_13; 
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_3 = x_13;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
block_20:
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
x_10 = x_19;
x_11 = x_18;
goto block_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
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
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
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
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_array_size(x_3);
x_11 = lean_box_usize(x_10);
x_12 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1;
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0___boxed), 9, 4);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_11);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_9);
x_14 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
return x_12;
}
}
static lean_object* _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after unifyEqs\n", 15, 15);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("before unifyEqs\n", 16, 16);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_19 = x_10;
} else {
 lean_dec_ref(x_10);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_22 = x_9;
} else {
 lean_dec_ref(x_9);
 x_22 = lean_box(0);
}
x_43 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_44 = lean_array_get(x_2, x_43, x_20);
x_45 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_3);
x_46 = l_Lean_Meta_introNCore(x_17, x_44, x_3, x_4, x_45, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec_ref(x_46);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
lean_inc(x_8);
x_127 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_13, x_48);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_unbox(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec_ref(x_127);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_51 = x_11;
x_52 = x_12;
x_53 = x_13;
x_54 = x_14;
x_55 = x_130;
goto block_126;
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_127);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_127, 1);
x_133 = lean_ctor_get(x_127, 0);
lean_dec(x_133);
x_134 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3;
lean_inc(x_49);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_49);
lean_ctor_set_tag(x_127, 7);
lean_ctor_set(x_127, 1, x_135);
lean_ctor_set(x_127, 0, x_134);
x_136 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_8);
x_138 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_137, x_11, x_12, x_13, x_14, x_132);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec_ref(x_138);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_51 = x_11;
x_52 = x_12;
x_53 = x_13;
x_54 = x_14;
x_55 = x_139;
goto block_126;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_140 = lean_ctor_get(x_127, 1);
lean_inc(x_140);
lean_dec(x_127);
x_141 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3;
lean_inc(x_49);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_49);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_inc(x_8);
x_146 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_145, x_11, x_12, x_13, x_14, x_140);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec_ref(x_146);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_51 = x_11;
x_52 = x_12;
x_53 = x_13;
x_54 = x_14;
x_55 = x_147;
goto block_126;
}
}
block_126:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_5);
x_57 = lean_nat_add(x_6, x_56);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = lean_box(0);
lean_inc(x_54);
lean_inc_ref(x_53);
lean_inc(x_52);
lean_inc_ref(x_51);
x_60 = l_Lean_Meta_Cases_unifyEqs_x3f(x_57, x_49, x_58, x_59, x_51, x_52, x_53, x_54, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_22);
lean_dec(x_19);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_20, x_63);
lean_dec(x_20);
if (lean_is_scalar(x_50)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_50;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_21);
x_9 = x_65;
x_10 = x_18;
x_15 = x_62;
goto _start;
}
else
{
uint8_t x_67; 
lean_dec(x_50);
x_67 = !lean_is_exclusive(x_61);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_61, 0);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_dec_ref(x_60);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_68, 0);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_8);
x_73 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_53, x_69);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_free_object(x_68);
lean_free_object(x_61);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec_ref(x_73);
x_23 = x_71;
x_24 = x_72;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_76;
goto block_42;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_73, 1);
x_79 = lean_ctor_get(x_73, 0);
lean_dec(x_79);
x_80 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_71);
lean_ctor_set(x_61, 0, x_71);
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set(x_73, 0, x_80);
x_81 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_81);
lean_ctor_set(x_68, 0, x_73);
lean_inc(x_8);
x_82 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_68, x_51, x_52, x_53, x_54, x_78);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_23 = x_71;
x_24 = x_72;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_83;
goto block_42;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_dec(x_73);
x_85 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_71);
lean_ctor_set(x_61, 0, x_71);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_61);
x_87 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_87);
lean_ctor_set(x_68, 0, x_86);
lean_inc(x_8);
x_88 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_68, x_51, x_52, x_53, x_54, x_84);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec_ref(x_88);
x_23 = x_71;
x_24 = x_72;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_89;
goto block_42;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_68, 0);
x_91 = lean_ctor_get(x_68, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_68);
lean_inc(x_8);
x_92 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_53, x_69);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_free_object(x_61);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec_ref(x_92);
x_23 = x_90;
x_24 = x_91;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_95;
goto block_42;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_97 = x_92;
} else {
 lean_dec_ref(x_92);
 x_97 = lean_box(0);
}
x_98 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_90);
lean_ctor_set(x_61, 0, x_90);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(7, 2, 0);
} else {
 x_99 = x_97;
 lean_ctor_set_tag(x_99, 7);
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_61);
x_100 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_inc(x_8);
x_102 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_101, x_51, x_52, x_53, x_54, x_96);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec_ref(x_102);
x_23 = x_90;
x_24 = x_91;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_103;
goto block_42;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_104 = lean_ctor_get(x_61, 0);
lean_inc(x_104);
lean_dec(x_61);
x_105 = lean_ctor_get(x_60, 1);
lean_inc(x_105);
lean_dec_ref(x_60);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
lean_inc(x_8);
x_109 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_53, x_105);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_108);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec_ref(x_109);
x_23 = x_106;
x_24 = x_107;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_112;
goto block_42;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_114 = x_109;
} else {
 lean_dec_ref(x_109);
 x_114 = lean_box(0);
}
x_115 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_106);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_106);
if (lean_is_scalar(x_114)) {
 x_117 = lean_alloc_ctor(7, 2, 0);
} else {
 x_117 = x_114;
 lean_ctor_set_tag(x_117, 7);
}
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
if (lean_is_scalar(x_108)) {
 x_119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_119 = x_108;
 lean_ctor_set_tag(x_119, 7);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_8);
x_120 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_119, x_51, x_52, x_53, x_54, x_113);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec_ref(x_120);
x_23 = x_106;
x_24 = x_107;
x_25 = x_51;
x_26 = x_52;
x_27 = x_53;
x_28 = x_54;
x_29 = x_121;
goto block_42;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_60);
if (x_122 == 0)
{
return x_60;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_60, 0);
x_124 = lean_ctor_get(x_60, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_60);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_148 = !lean_is_exclusive(x_46);
if (x_148 == 0)
{
return x_46;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_46, 0);
x_150 = lean_ctor_get(x_46, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_46);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
block_42:
{
lean_object* x_30; 
lean_inc_ref(x_7);
x_30 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(x_23, x_24, x_7, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_20, x_33);
lean_dec(x_20);
if (lean_is_scalar(x_19)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_19;
}
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_21);
if (lean_is_scalar(x_22)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_22;
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_9 = x_36;
x_10 = x_18;
x_15 = x_32;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after check splitter", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_3, x_4, x_3, x_4, x_5, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_50; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Expr_app___override(x_6, x_21);
x_24 = l_Lean_mkAppN(x_23, x_1);
lean_dec_ref(x_1);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_24);
x_50 = l_Lean_Meta_check(x_24, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec_ref(x_50);
lean_inc(x_7);
x_52 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_7, x_17, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec_ref(x_52);
x_25 = x_15;
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_55;
goto block_49;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec_ref(x_52);
x_57 = l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2;
lean_inc(x_7);
x_58 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_7, x_57, x_15, x_16, x_17, x_18, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_25 = x_15;
x_26 = x_16;
x_27 = x_17;
x_28 = x_18;
x_29 = x_59;
goto block_49;
}
}
else
{
uint8_t x_60; 
lean_dec_ref(x_24);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_60 = !lean_is_exclusive(x_50);
if (x_60 == 0)
{
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
block_49:
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Meta_Match_MatchEqns_size(x_8);
lean_inc(x_28);
lean_inc_ref(x_27);
lean_inc(x_26);
lean_inc_ref(x_25);
x_31 = l_Lean_MVarId_applyN(x_9, x_24, x_30, x_4, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0;
x_35 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0(x_8, x_10, x_11, x_3, x_12, x_13, x_14, x_7, x_34, x_32, x_25, x_26, x_27, x_28, x_33);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_List_reverse___redArg(x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_List_reverse___redArg(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
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
else
{
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
return x_31;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_64 = !lean_is_exclusive(x_20);
if (x_64 == 0)
{
return x_20;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_20, 0);
x_66 = lean_ctor_get(x_20, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_20);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrEqs after generalizeTargetsEq: ", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_1, x_5, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec_ref(x_8);
x_18 = l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1;
x_19 = lean_array_size(x_2);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_19, x_20, x_2);
x_22 = lean_array_to_list(x_21);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at_____private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(x_22, x_23);
x_25 = l_Lean_MessageData_ofList(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_1, x_28, x_3, x_4, x_5, x_6, x_17);
return x_29;
}
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: `", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` is not an auxiliary declaration used to encode `match`-expressions\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 176, 176);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`split` tactic failed to split a match-expression: the splitter auxiliary theorem `", 83, 83);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` can only eliminate into `Prop`", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after introN\n", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after generalize\n", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("after generalizeMatchDiscrs\n", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("applyMatchSplitter\n", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_applyMatchSplitter___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_applyMatchSplitter___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_2);
x_11 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_2, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = l_Lean_Meta_Split_applyMatchSplitter___closed__1;
x_17 = l_Lean_MessageData_ofName(x_2);
lean_ctor_set_tag(x_11, 7);
lean_ctor_set(x_11, 1, x_17);
lean_ctor_set(x_11, 0, x_16);
x_18 = l_Lean_Meta_Split_applyMatchSplitter___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_19, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Meta_Split_applyMatchSplitter___closed__1;
x_23 = l_Lean_MessageData_ofName(x_2);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_Split_applyMatchSplitter___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_26, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_29 = x_11;
} else {
 lean_dec_ref(x_11);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_31 = x_12;
} else {
 lean_dec_ref(x_12);
 x_31 = lean_box(0);
}
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_2);
x_32 = lean_get_match_equations_for(x_2, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_inc_ref(x_3);
x_36 = lean_array_to_list(x_3);
lean_inc(x_35);
x_37 = l_Lean_Expr_const___override(x_35, x_36);
x_38 = l_Lean_mkAppN(x_37, x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_39 = lean_infer_type(x_38, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_42 = l_Lean_Meta_whnfForall(x_40, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_279; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_46 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_8, x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = lean_unsigned_to_nat(0u);
x_177 = l_Lean_Expr_bindingDomain_x21(x_43);
lean_dec(x_43);
x_279 = lean_unbox(x_47);
lean_dec(x_47);
if (x_279 == 0)
{
x_225 = x_6;
x_226 = x_7;
x_227 = x_8;
x_228 = x_9;
x_229 = x_48;
goto block_278;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_280 = l_Lean_Meta_Split_applyMatchSplitter___closed__15;
lean_inc(x_1);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_1);
x_282 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
x_283 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_284, x_6, x_7, x_8, x_9, x_48);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec_ref(x_285);
x_225 = x_6;
x_226 = x_7;
x_227 = x_8;
x_228 = x_9;
x_229 = x_286;
goto block_278;
}
block_75:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_array_to_list(x_59);
x_66 = l_Lean_Expr_const___override(x_35, x_65);
x_67 = l_Lean_mkAppN(x_66, x_4);
x_68 = 1;
x_69 = 1;
x_70 = lean_box(x_55);
x_71 = lean_box(x_68);
x_72 = lean_box(x_69);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__0___boxed), 19, 14);
lean_closure_set(x_73, 0, x_51);
lean_closure_set(x_73, 1, x_57);
lean_closure_set(x_73, 2, x_70);
lean_closure_set(x_73, 3, x_71);
lean_closure_set(x_73, 4, x_72);
lean_closure_set(x_73, 5, x_67);
lean_closure_set(x_73, 6, x_45);
lean_closure_set(x_73, 7, x_33);
lean_closure_set(x_73, 8, x_54);
lean_closure_set(x_73, 9, x_50);
lean_closure_set(x_73, 10, x_56);
lean_closure_set(x_73, 11, x_30);
lean_closure_set(x_73, 12, x_53);
lean_closure_set(x_73, 13, x_52);
x_74 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_58, x_73, x_60, x_61, x_62, x_63, x_64);
return x_74;
}
block_120:
{
lean_object* x_89; 
lean_inc(x_82);
x_89 = l_Lean_MVarId_getType(x_82, x_84, x_85, x_86, x_87, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec_ref(x_89);
lean_inc(x_90);
x_92 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel), 6, 1);
lean_closure_set(x_92, 0, x_90);
lean_inc(x_87);
lean_inc_ref(x_86);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_82);
x_93 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_82, x_92, x_84, x_85, x_86, x_87, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; size_t x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_ctor_get(x_30, 3);
lean_inc(x_96);
x_97 = lean_array_size(x_83);
x_98 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_97, x_81, x_83);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_99; 
x_99 = l_Lean_Level_isZero(x_94);
lean_dec(x_94);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec_ref(x_98);
lean_dec(x_90);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_33);
lean_dec(x_30);
lean_dec_ref(x_3);
x_100 = l_Lean_Meta_Split_applyMatchSplitter___closed__5;
x_101 = l_Lean_MessageData_ofName(x_35);
if (lean_is_scalar(x_49)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_49;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Meta_Split_applyMatchSplitter___closed__7;
if (lean_is_scalar(x_29)) {
 x_104 = lean_alloc_ctor(7, 2, 0);
} else {
 x_104 = x_29;
 lean_ctor_set_tag(x_104, 7);
}
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_104, x_84, x_85, x_86, x_87, x_95);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
else
{
lean_dec(x_49);
lean_dec(x_29);
x_51 = x_98;
x_52 = x_76;
x_53 = x_78;
x_54 = x_77;
x_55 = x_79;
x_56 = x_80;
x_57 = x_90;
x_58 = x_82;
x_59 = x_3;
x_60 = x_84;
x_61 = x_85;
x_62 = x_86;
x_63 = x_87;
x_64 = x_95;
goto block_75;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_49);
lean_dec(x_29);
x_110 = lean_ctor_get(x_96, 0);
lean_inc(x_110);
lean_dec(x_96);
x_111 = lean_array_set(x_3, x_110, x_94);
lean_dec(x_110);
x_51 = x_98;
x_52 = x_76;
x_53 = x_78;
x_54 = x_77;
x_55 = x_79;
x_56 = x_80;
x_57 = x_90;
x_58 = x_82;
x_59 = x_111;
x_60 = x_84;
x_61 = x_85;
x_62 = x_86;
x_63 = x_87;
x_64 = x_95;
goto block_75;
}
}
else
{
uint8_t x_112; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_3);
x_112 = !lean_is_exclusive(x_93);
if (x_112 == 0)
{
return x_93;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_93, 0);
x_114 = lean_ctor_get(x_93, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_93);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec_ref(x_76);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_3);
x_116 = !lean_is_exclusive(x_89);
if (x_116 == 0)
{
return x_89;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_89, 0);
x_118 = lean_ctor_get(x_89, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_89);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
block_176:
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_129 = lean_array_get_size(x_5);
lean_dec_ref(x_5);
x_130 = lean_box(0);
x_131 = 0;
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_129);
x_132 = l_Lean_Meta_introNCore(x_123, x_129, x_130, x_131, x_131, x_124, x_125, x_126, x_127, x_128);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec_ref(x_132);
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_133, 0);
x_137 = lean_ctor_get(x_133, 1);
x_138 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_126, x_134);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
lean_free_object(x_133);
lean_dec(x_31);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec_ref(x_138);
lean_inc(x_137);
x_76 = x_121;
x_77 = x_137;
x_78 = x_129;
x_79 = x_131;
x_80 = x_130;
x_81 = x_122;
x_82 = x_137;
x_83 = x_136;
x_84 = x_124;
x_85 = x_125;
x_86 = x_126;
x_87 = x_127;
x_88 = x_141;
goto block_120;
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_138);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_138, 1);
x_144 = lean_ctor_get(x_138, 0);
lean_dec(x_144);
x_145 = l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_inc(x_137);
if (lean_is_scalar(x_31)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_31;
}
lean_ctor_set(x_146, 0, x_137);
lean_ctor_set_tag(x_138, 7);
lean_ctor_set(x_138, 1, x_146);
lean_ctor_set(x_138, 0, x_145);
x_147 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_133, 7);
lean_ctor_set(x_133, 1, x_147);
lean_ctor_set(x_133, 0, x_138);
x_148 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_133, x_124, x_125, x_126, x_127, x_143);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
lean_inc(x_137);
x_76 = x_121;
x_77 = x_137;
x_78 = x_129;
x_79 = x_131;
x_80 = x_130;
x_81 = x_122;
x_82 = x_137;
x_83 = x_136;
x_84 = x_124;
x_85 = x_125;
x_86 = x_126;
x_87 = x_127;
x_88 = x_149;
goto block_120;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_150 = lean_ctor_get(x_138, 1);
lean_inc(x_150);
lean_dec(x_138);
x_151 = l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_inc(x_137);
if (lean_is_scalar(x_31)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_31;
}
lean_ctor_set(x_152, 0, x_137);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_133, 7);
lean_ctor_set(x_133, 1, x_154);
lean_ctor_set(x_133, 0, x_153);
x_155 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_133, x_124, x_125, x_126, x_127, x_150);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec_ref(x_155);
lean_inc(x_137);
x_76 = x_121;
x_77 = x_137;
x_78 = x_129;
x_79 = x_131;
x_80 = x_130;
x_81 = x_122;
x_82 = x_137;
x_83 = x_136;
x_84 = x_124;
x_85 = x_125;
x_86 = x_126;
x_87 = x_127;
x_88 = x_156;
goto block_120;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_157 = lean_ctor_get(x_133, 0);
x_158 = lean_ctor_get(x_133, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_133);
x_159 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_126, x_134);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_31);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
lean_dec_ref(x_159);
lean_inc(x_158);
x_76 = x_121;
x_77 = x_158;
x_78 = x_129;
x_79 = x_131;
x_80 = x_130;
x_81 = x_122;
x_82 = x_158;
x_83 = x_157;
x_84 = x_124;
x_85 = x_125;
x_86 = x_126;
x_87 = x_127;
x_88 = x_162;
goto block_120;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_164 = x_159;
} else {
 lean_dec_ref(x_159);
 x_164 = lean_box(0);
}
x_165 = l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_inc(x_158);
if (lean_is_scalar(x_31)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_31;
}
lean_ctor_set(x_166, 0, x_158);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_164;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_169, x_124, x_125, x_126, x_127, x_163);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec_ref(x_170);
lean_inc(x_158);
x_76 = x_121;
x_77 = x_158;
x_78 = x_129;
x_79 = x_131;
x_80 = x_130;
x_81 = x_122;
x_82 = x_158;
x_83 = x_157;
x_84 = x_124;
x_85 = x_125;
x_86 = x_126;
x_87 = x_127;
x_88 = x_171;
goto block_120;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_129);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec_ref(x_121);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_3);
x_172 = !lean_is_exclusive(x_132);
if (x_172 == 0)
{
return x_132;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_132, 0);
x_174 = lean_ctor_get(x_132, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_132);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
block_224:
{
size_t x_187; size_t x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_array_size(x_179);
x_188 = 0;
x_189 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_187, x_188, x_179);
lean_inc(x_185);
lean_inc_ref(x_184);
lean_inc(x_183);
lean_inc_ref(x_182);
x_190 = l_Lean_Meta_generalizeTargetsEq(x_181, x_177, x_189, x_182, x_183, x_184, x_185, x_186);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec_ref(x_190);
lean_inc(x_185);
lean_inc_ref(x_184);
lean_inc(x_183);
lean_inc_ref(x_182);
lean_inc(x_191);
x_193 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_191, x_180, x_182, x_183, x_184, x_185, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_184, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec_ref(x_195);
x_121 = x_178;
x_122 = x_188;
x_123 = x_191;
x_124 = x_182;
x_125 = x_183;
x_126 = x_184;
x_127 = x_185;
x_128 = x_198;
goto block_176;
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_195);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_200 = lean_ctor_get(x_195, 1);
x_201 = lean_ctor_get(x_195, 0);
lean_dec(x_201);
x_202 = l_Lean_Meta_Split_applyMatchSplitter___closed__11;
lean_inc(x_191);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_191);
lean_ctor_set_tag(x_195, 7);
lean_ctor_set(x_195, 1, x_203);
lean_ctor_set(x_195, 0, x_202);
x_204 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_205 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_205, x_182, x_183, x_184, x_185, x_200);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec_ref(x_206);
x_121 = x_178;
x_122 = x_188;
x_123 = x_191;
x_124 = x_182;
x_125 = x_183;
x_126 = x_184;
x_127 = x_185;
x_128 = x_207;
goto block_176;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_195, 1);
lean_inc(x_208);
lean_dec(x_195);
x_209 = l_Lean_Meta_Split_applyMatchSplitter___closed__11;
lean_inc(x_191);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_191);
x_211 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_213, x_182, x_183, x_184, x_185, x_208);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec_ref(x_214);
x_121 = x_178;
x_122 = x_188;
x_123 = x_191;
x_124 = x_182;
x_125 = x_183;
x_126 = x_184;
x_127 = x_185;
x_128 = x_215;
goto block_176;
}
}
}
else
{
uint8_t x_216; 
lean_dec(x_191);
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec_ref(x_178);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_216 = !lean_is_exclusive(x_193);
if (x_216 == 0)
{
return x_193;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_193, 0);
x_218 = lean_ctor_get(x_193, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_193);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_185);
lean_dec_ref(x_184);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_180);
lean_dec_ref(x_178);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_220 = !lean_is_exclusive(x_190);
if (x_220 == 0)
{
return x_190;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_190, 0);
x_222 = lean_ctor_get(x_190, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_190);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
block_278:
{
lean_object* x_230; 
lean_inc(x_228);
lean_inc_ref(x_227);
lean_inc(x_226);
lean_inc_ref(x_225);
lean_inc_ref(x_5);
lean_inc_ref(x_177);
x_230 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(x_1, x_2, x_177, x_5, x_225, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec_ref(x_230);
x_234 = lean_ctor_get(x_231, 0);
lean_inc(x_234);
lean_dec(x_231);
x_235 = !lean_is_exclusive(x_232);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_236 = lean_ctor_get(x_232, 0);
x_237 = lean_ctor_get(x_232, 1);
x_238 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_227, x_233);
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_236);
x_242 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed), 7, 2);
lean_closure_set(x_242, 0, x_45);
lean_closure_set(x_242, 1, x_236);
x_243 = lean_unbox(x_240);
lean_dec(x_240);
if (x_243 == 0)
{
lean_free_object(x_238);
lean_free_object(x_232);
x_178 = x_236;
x_179 = x_234;
x_180 = x_242;
x_181 = x_237;
x_182 = x_225;
x_183 = x_226;
x_184 = x_227;
x_185 = x_228;
x_186 = x_241;
goto block_224;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_244 = l_Lean_Meta_Split_applyMatchSplitter___closed__13;
lean_inc(x_237);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_237);
lean_ctor_set_tag(x_238, 7);
lean_ctor_set(x_238, 1, x_245);
lean_ctor_set(x_238, 0, x_244);
x_246 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_232, 7);
lean_ctor_set(x_232, 1, x_246);
lean_ctor_set(x_232, 0, x_238);
x_247 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_232, x_225, x_226, x_227, x_228, x_241);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec_ref(x_247);
x_178 = x_236;
x_179 = x_234;
x_180 = x_242;
x_181 = x_237;
x_182 = x_225;
x_183 = x_226;
x_184 = x_227;
x_185 = x_228;
x_186 = x_248;
goto block_224;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_249 = lean_ctor_get(x_238, 0);
x_250 = lean_ctor_get(x_238, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_238);
lean_inc(x_236);
x_251 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed), 7, 2);
lean_closure_set(x_251, 0, x_45);
lean_closure_set(x_251, 1, x_236);
x_252 = lean_unbox(x_249);
lean_dec(x_249);
if (x_252 == 0)
{
lean_free_object(x_232);
x_178 = x_236;
x_179 = x_234;
x_180 = x_251;
x_181 = x_237;
x_182 = x_225;
x_183 = x_226;
x_184 = x_227;
x_185 = x_228;
x_186 = x_250;
goto block_224;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_253 = l_Lean_Meta_Split_applyMatchSplitter___closed__13;
lean_inc(x_237);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_237);
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_232, 7);
lean_ctor_set(x_232, 1, x_256);
lean_ctor_set(x_232, 0, x_255);
x_257 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_232, x_225, x_226, x_227, x_228, x_250);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec_ref(x_257);
x_178 = x_236;
x_179 = x_234;
x_180 = x_251;
x_181 = x_237;
x_182 = x_225;
x_183 = x_226;
x_184 = x_227;
x_185 = x_228;
x_186 = x_258;
goto block_224;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_259 = lean_ctor_get(x_232, 0);
x_260 = lean_ctor_get(x_232, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_232);
x_261 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_227, x_233);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
lean_inc(x_259);
x_265 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed), 7, 2);
lean_closure_set(x_265, 0, x_45);
lean_closure_set(x_265, 1, x_259);
x_266 = lean_unbox(x_262);
lean_dec(x_262);
if (x_266 == 0)
{
lean_dec(x_264);
x_178 = x_259;
x_179 = x_234;
x_180 = x_265;
x_181 = x_260;
x_182 = x_225;
x_183 = x_226;
x_184 = x_227;
x_185 = x_228;
x_186 = x_263;
goto block_224;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = l_Lean_Meta_Split_applyMatchSplitter___closed__13;
lean_inc(x_260);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_260);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(7, 2, 0);
} else {
 x_269 = x_264;
 lean_ctor_set_tag(x_269, 7);
}
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_271 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_271, x_225, x_226, x_227, x_228, x_263);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec_ref(x_272);
x_178 = x_259;
x_179 = x_234;
x_180 = x_265;
x_181 = x_260;
x_182 = x_225;
x_183 = x_226;
x_184 = x_227;
x_185 = x_228;
x_186 = x_273;
goto block_224;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_177);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_274 = !lean_is_exclusive(x_230);
if (x_274 == 0)
{
return x_230;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_230, 0);
x_276 = lean_ctor_get(x_230, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_230);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
return x_277;
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_287 = !lean_is_exclusive(x_42);
if (x_287 == 0)
{
return x_42;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_42, 0);
x_289 = lean_ctor_get(x_42, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_42);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = !lean_is_exclusive(x_39);
if (x_291 == 0)
{
return x_39;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_39, 0);
x_293 = lean_ctor_get(x_39, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_39);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_32);
if (x_295 == 0)
{
return x_32;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_32, 0);
x_297 = lean_ctor_get(x_32, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_32);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
x_17 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___boxed(lean_object** _args) {
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
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_unbox(x_3);
x_21 = lean_unbox(x_4);
x_22 = lean_unbox(x_5);
x_23 = l_Lean_Meta_Split_applyMatchSplitter___lam__0(x_1, x_2, x_20, x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_8);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Split_applyMatchSplitter___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Split_applyMatchSplitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`split` tactic failed to generalize discriminant(s) at", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nresulting expression was not type correct\npossible solution: generalize discriminant(s) manually before using `split`", 118, 118);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1;
x_3 = l_Lean_indentExpr(x_1);
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_1);
x_8 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Split_throwDiscrGenError___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Split_throwDiscrGenError___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Split_throwDiscrGenError(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_19 = lean_array_get(x_2, x_18, x_16);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
x_20 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_14, x_3, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_16, x_23);
lean_dec(x_16);
lean_ctor_set(x_5, 1, x_17);
lean_ctor_set(x_5, 0, x_21);
lean_ctor_set(x_4, 1, x_5);
lean_ctor_set(x_4, 0, x_24);
x_5 = x_15;
x_10 = x_22;
goto _start;
}
else
{
uint8_t x_26; 
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_35 = lean_array_get(x_2, x_34, x_32);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
x_36 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_30, x_3, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_32, x_39);
lean_dec(x_32);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
x_4 = x_41;
x_5 = x_31;
x_10 = x_38;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_5);
lean_dec(x_31);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_45 = x_36;
} else {
 lean_dec_ref(x_36);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_5);
x_49 = lean_ctor_get(x_4, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_51 = x_4;
} else {
 lean_dec_ref(x_4);
 x_51 = lean_box(0);
}
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_53 = lean_array_get(x_2, x_52, x_49);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_3);
x_54 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_47, x_3, x_53, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_49, x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_50);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_4 = x_60;
x_5 = x_48;
x_10 = x_56;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_64 = x_54;
} else {
 lean_dec_ref(x_54);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: match application expected", 60, 60);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_splitMatch___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nthis error typically occurs when the `split` tactic internal functions have been used in a new meta-program", 108, 108);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_splitMatch___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_1);
x_10 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_Split_splitMatch___lam__0___closed__1;
x_14 = l_Lean_indentExpr(x_1);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Split_splitMatch___lam__0___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_17, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec_ref(x_10);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_19, 4);
lean_inc_ref(x_23);
x_24 = lean_ctor_get(x_19, 6);
lean_inc_ref(x_24);
lean_dec(x_19);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_21);
x_25 = lean_get_match_equations_for(x_21, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_21);
x_28 = l_Lean_Meta_Split_applyMatchSplitter(x_3, x_21, x_22, x_23, x_24, x_5, x_6, x_7, x_8, x_27);
lean_dec_ref(x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0;
x_32 = l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0(x_26, x_4, x_21, x_31, x_29, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_26);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_List_reverse___redArg(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_List_reverse___redArg(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_28;
}
}
else
{
uint8_t x_46; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_50 = !lean_is_exclusive(x_10);
if (x_50 == 0)
{
return x_10;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_10, 0);
x_52 = lean_ctor_get(x_10, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_10);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = 0;
x_10 = lean_box(x_9);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Split_splitMatch___lam__0___boxed), 9, 4);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_8);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_Meta_Split_splitMatch___lam__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failure", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__0;
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`split` tactic failed at", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("did not find term to split\n", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f_go___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_177; 
if (x_2 == 0)
{
uint8_t x_244; 
x_244 = 1;
x_177 = x_244;
goto block_243;
}
else
{
uint8_t x_245; 
x_245 = 2;
x_177 = x_245;
goto block_243;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_72:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Meta_splitIfTarget_x3f(x_1, x_16, x_3, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_17);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_17, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 1);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set_tag(x_28, 1);
lean_ctor_set(x_28, 1, x_35);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_28);
lean_ctor_set(x_18, 0, x_27);
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_38);
lean_ctor_set(x_18, 0, x_27);
return x_17;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_41 = x_28;
} else {
 lean_dec_ref(x_28);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_41;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_18, 0, x_44);
return x_17;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_ctor_get(x_27, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_47 = x_27;
} else {
 lean_dec_ref(x_27);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_28, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_49 = x_28;
} else {
 lean_dec_ref(x_28);
 x_49 = lean_box(0);
}
x_50 = lean_box(0);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_49;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_47)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_47;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_18, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_18);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_54 = lean_ctor_get(x_18, 0);
lean_inc(x_54);
lean_dec(x_18);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_17, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_58 = x_17;
} else {
 lean_dec_ref(x_17);
 x_58 = lean_box(0);
}
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_62;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_60;
 lean_ctor_set_tag(x_65, 1);
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_58)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_58;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
return x_67;
}
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_17);
if (x_68 == 0)
{
return x_17;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_17, 0);
x_70 = lean_ctor_get(x_17, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_17);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
block_130:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; size_t x_93; lean_object* x_94; uint8_t x_95; 
x_79 = lean_ctor_get(x_5, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_80);
x_81 = lean_array_get_size(x_80);
x_82 = l_Lean_Expr_hash(x_73);
x_83 = 32;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = 16;
x_87 = lean_uint64_shift_right(x_85, x_86);
x_88 = lean_uint64_xor(x_85, x_87);
x_89 = lean_uint64_to_usize(x_88);
x_90 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_91 = 1;
x_92 = lean_usize_sub(x_90, x_91);
x_93 = lean_usize_land(x_89, x_92);
x_94 = lean_array_uget(x_80, x_93);
x_95 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0___redArg(x_73, x_94);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_5);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_97 = lean_ctor_get(x_5, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_5, 0);
lean_dec(x_98);
x_99 = lean_box(0);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_79, x_100);
lean_dec(x_79);
x_102 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_102, 0, x_73);
lean_ctor_set(x_102, 1, x_99);
lean_ctor_set(x_102, 2, x_94);
x_103 = lean_array_uset(x_80, x_93, x_102);
x_104 = lean_unsigned_to_nat(4u);
x_105 = lean_nat_mul(x_101, x_104);
x_106 = lean_unsigned_to_nat(3u);
x_107 = lean_nat_div(x_105, x_106);
lean_dec(x_105);
x_108 = lean_array_get_size(x_103);
x_109 = lean_nat_dec_le(x_107, x_108);
lean_dec(x_108);
lean_dec(x_107);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_103);
lean_ctor_set(x_5, 1, x_110);
lean_ctor_set(x_5, 0, x_101);
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
x_10 = x_78;
goto _start;
}
else
{
lean_ctor_set(x_5, 1, x_103);
lean_ctor_set(x_5, 0, x_101);
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
x_10 = x_78;
goto _start;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_5);
x_113 = lean_box(0);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_nat_add(x_79, x_114);
lean_dec(x_79);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_73);
lean_ctor_set(x_116, 1, x_113);
lean_ctor_set(x_116, 2, x_94);
x_117 = lean_array_uset(x_80, x_93, x_116);
x_118 = lean_unsigned_to_nat(4u);
x_119 = lean_nat_mul(x_115, x_118);
x_120 = lean_unsigned_to_nat(3u);
x_121 = lean_nat_div(x_119, x_120);
lean_dec(x_119);
x_122 = lean_array_get_size(x_117);
x_123 = lean_nat_dec_le(x_121, x_122);
lean_dec(x_122);
lean_dec(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_117);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_115);
lean_ctor_set(x_125, 1, x_124);
x_5 = x_125;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
x_10 = x_78;
goto _start;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_115);
lean_ctor_set(x_127, 1, x_117);
x_5 = x_127;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
x_10 = x_78;
goto _start;
}
}
}
else
{
lean_dec(x_94);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec_ref(x_73);
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
x_10 = x_78;
goto _start;
}
}
block_176:
{
if (x_135 == 0)
{
uint8_t x_136; 
lean_dec_ref(x_133);
x_136 = l_Lean_Meta_Split_isDiscrGenException(x_132);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_137 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_138 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_137, x_8, x_134);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec_ref(x_132);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec_ref(x_138);
x_73 = x_131;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_141;
goto block_130;
}
else
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_138);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_143 = lean_ctor_get(x_138, 1);
x_144 = lean_ctor_get(x_138, 0);
lean_dec(x_144);
x_145 = l_Lean_Meta_splitTarget_x3f_go___closed__3;
lean_inc_ref(x_131);
x_146 = l_Lean_indentExpr(x_131);
lean_ctor_set_tag(x_138, 7);
lean_ctor_set(x_138, 1, x_146);
lean_ctor_set(x_138, 0, x_145);
x_147 = l_Lean_Meta_splitTarget_x3f_go___closed__5;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_138);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Lean_Exception_toMessageData(x_132);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_137, x_152, x_6, x_7, x_8, x_9, x_143);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec_ref(x_153);
x_73 = x_131;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_154;
goto block_130;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_138, 1);
lean_inc(x_155);
lean_dec(x_138);
x_156 = l_Lean_Meta_splitTarget_x3f_go___closed__3;
lean_inc_ref(x_131);
x_157 = l_Lean_indentExpr(x_131);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_Meta_splitTarget_x3f_go___closed__5;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_Exception_toMessageData(x_132);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_137, x_164, x_6, x_7, x_8, x_9, x_155);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec_ref(x_165);
x_73 = x_131;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_166;
goto block_130;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
lean_dec_ref(x_132);
x_167 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_168 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_167, x_8, x_134);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec_ref(x_168);
x_73 = x_131;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_171;
goto block_130;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
lean_dec_ref(x_168);
lean_inc_ref(x_131);
x_173 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_131);
x_174 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_167, x_173, x_6, x_7, x_8, x_9, x_172);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec_ref(x_174);
x_73 = x_131;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_9;
x_78 = x_175;
goto block_130;
}
}
}
else
{
lean_dec_ref(x_132);
lean_dec_ref(x_131);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_133;
}
}
block_243:
{
lean_object* x_178; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_4);
x_178 = l_Lean_Meta_findSplit_x3f(x_4, x_177, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec_ref(x_178);
x_181 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_182 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_181, x_8, x_180);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_unbox(x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_1);
x_185 = lean_ctor_get(x_182, 1);
lean_inc(x_185);
lean_dec_ref(x_182);
x_11 = x_185;
goto block_14;
}
else
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_182);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_182, 1);
x_188 = lean_ctor_get(x_182, 0);
lean_dec(x_188);
x_189 = l_Lean_Meta_splitTarget_x3f_go___closed__7;
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set_tag(x_182, 7);
lean_ctor_set(x_182, 1, x_190);
lean_ctor_set(x_182, 0, x_189);
x_191 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_182);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_181, x_192, x_6, x_7, x_8, x_9, x_187);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec_ref(x_193);
x_11 = x_194;
goto block_14;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_195 = lean_ctor_get(x_182, 1);
lean_inc(x_195);
lean_dec(x_182);
x_196 = l_Lean_Meta_splitTarget_x3f_go___closed__7;
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_1);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_181, x_200, x_6, x_7, x_8, x_9, x_195);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec_ref(x_201);
x_11 = x_202;
goto block_14;
}
}
}
else
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_178, 1);
lean_inc(x_203);
lean_dec_ref(x_178);
x_204 = !lean_is_exclusive(x_179);
if (x_204 == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_179, 0);
x_206 = l_Lean_Expr_isIte(x_205);
if (x_206 == 0)
{
uint8_t x_207; 
x_207 = l_Lean_Expr_isDIte(x_205);
if (x_207 == 0)
{
lean_object* x_208; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_205);
lean_inc(x_1);
x_208 = l_Lean_Meta_Split_splitMatch(x_1, x_205, x_6, x_7, x_8, x_9, x_203);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
lean_dec(x_205);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_208, 0);
lean_ctor_set(x_179, 0, x_210);
lean_ctor_set(x_208, 0, x_179);
return x_208;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_208, 0);
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_208);
lean_ctor_set(x_179, 0, x_211);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_179);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
else
{
uint8_t x_214; 
lean_free_object(x_179);
x_214 = !lean_is_exclusive(x_208);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = lean_ctor_get(x_208, 0);
x_216 = lean_ctor_get(x_208, 1);
lean_inc(x_216);
lean_inc(x_215);
x_217 = l_Lean_Exception_isInterrupt(x_215);
if (x_217 == 0)
{
uint8_t x_218; 
x_218 = l_Lean_Exception_isRuntime(x_215);
x_131 = x_205;
x_132 = x_215;
x_133 = x_208;
x_134 = x_216;
x_135 = x_218;
goto block_176;
}
else
{
x_131 = x_205;
x_132 = x_215;
x_133 = x_208;
x_134 = x_216;
x_135 = x_217;
goto block_176;
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_208, 0);
x_220 = lean_ctor_get(x_208, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_208);
lean_inc(x_220);
lean_inc(x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_Exception_isInterrupt(x_219);
if (x_222 == 0)
{
uint8_t x_223; 
x_223 = l_Lean_Exception_isRuntime(x_219);
x_131 = x_205;
x_132 = x_219;
x_133 = x_221;
x_134 = x_220;
x_135 = x_223;
goto block_176;
}
else
{
x_131 = x_205;
x_132 = x_219;
x_133 = x_221;
x_134 = x_220;
x_135 = x_222;
goto block_176;
}
}
}
}
else
{
lean_free_object(x_179);
lean_dec(x_205);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = x_203;
goto block_72;
}
}
else
{
lean_free_object(x_179);
lean_dec(x_205);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = x_203;
goto block_72;
}
}
else
{
lean_object* x_224; uint8_t x_225; 
x_224 = lean_ctor_get(x_179, 0);
lean_inc(x_224);
lean_dec(x_179);
x_225 = l_Lean_Expr_isIte(x_224);
if (x_225 == 0)
{
uint8_t x_226; 
x_226 = l_Lean_Expr_isDIte(x_224);
if (x_226 == 0)
{
lean_object* x_227; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_224);
lean_inc(x_1);
x_227 = l_Lean_Meta_Split_splitMatch(x_1, x_224, x_6, x_7, x_8, x_9, x_203);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_224);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
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
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_228);
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_229);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_233 = lean_ctor_get(x_227, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_227, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_235 = x_227;
} else {
 lean_dec_ref(x_227);
 x_235 = lean_box(0);
}
lean_inc(x_234);
lean_inc(x_233);
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
x_237 = l_Lean_Exception_isInterrupt(x_233);
if (x_237 == 0)
{
uint8_t x_238; 
x_238 = l_Lean_Exception_isRuntime(x_233);
x_131 = x_224;
x_132 = x_233;
x_133 = x_236;
x_134 = x_234;
x_135 = x_238;
goto block_176;
}
else
{
x_131 = x_224;
x_132 = x_233;
x_133 = x_236;
x_134 = x_234;
x_135 = x_237;
goto block_176;
}
}
}
else
{
lean_dec(x_224);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = x_203;
goto block_72;
}
}
else
{
lean_dec(x_224);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_15 = x_203;
goto block_72;
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_178);
if (x_239 == 0)
{
return x_178;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_178, 0);
x_241 = lean_ctor_get(x_178, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_178);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_10, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__4;
x_16 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_2, x_3, x_13, x_15, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(x_2);
x_10 = lean_box(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_splitTarget_x3f___lam__0___boxed), 8, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1), 8, 3);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_11);
x_13 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_splitTarget_x3f___lam__0(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_splitTarget_x3f(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_10 = l_List_reverse___redArg(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_box(0);
x_16 = 1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_17 = l_Lean_Meta_introNCore(x_13, x_1, x_15, x_2, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_20);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_19;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_3, 0);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_3);
x_28 = lean_box(0);
x_29 = 1;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_30 = l_Lean_Meta_introNCore(x_26, x_1, x_28, x_2, x_29, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
x_3 = x_27;
x_4 = x_34;
x_9 = x_32;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_9 = l_List_reverse___redArg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_14 = l_Lean_Meta_intro1Core(x_12, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_17);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_25 = l_Lean_Meta_intro1Core(x_23, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
x_2 = x_24;
x_3 = x_29;
x_8 = x_27;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_31 = lean_ctor_get(x_25, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_33 = x_25;
} else {
 lean_dec_ref(x_25);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_19; lean_object* x_20; lean_object* x_24; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_24 = l_Lean_MVarId_revert(x_1, x_2, x_3, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_29 = l_Lean_Meta_Split_splitMatch(x_28, x_4, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_array_get_size(x_27);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(x_32, x_3, x_30, x_33, x_5, x_6, x_7, x_8, x_31);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec_ref(x_34);
x_19 = x_42;
x_20 = x_43;
goto block_23;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec_ref(x_29);
x_19 = x_44;
x_20 = x_45;
goto block_23;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec_ref(x_24);
x_19 = x_46;
x_20 = x_47;
goto block_23;
}
block_18:
{
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Meta_Split_isDiscrGenException(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_11);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
block_23:
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
x_10 = x_20;
x_11 = x_19;
x_12 = x_22;
goto block_18;
}
else
{
x_10 = x_20;
x_11 = x_19;
x_12 = x_21;
goto block_18;
}
}
}
}
static lean_object* _init_l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_10, x_5, x_11);
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
x_16 = 2;
x_17 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__4;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_18 = l_Lean_Meta_findSplit_x3f(x_13, x_16, x_17, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_42; lean_object* x_43; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_82; lean_object* x_83; uint8_t x_92; uint8_t x_168; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_27 = x_18;
} else {
 lean_dec_ref(x_18);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_168 = l_Lean_Expr_isIte(x_28);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = l_Lean_Expr_isDIte(x_28);
x_92 = x_169;
goto block_167;
}
else
{
x_92 = x_168;
goto block_167;
}
block_41:
{
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Meta_Split_isDiscrGenException(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_27)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_27;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; uint8_t x_36; 
lean_dec_ref(x_31);
lean_dec(x_27);
x_35 = l_Lean_Meta_Split_throwDiscrGenError___redArg(x_28, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
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
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
if (lean_is_scalar(x_27)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_27;
 lean_ctor_set_tag(x_40, 1);
}
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_30);
return x_40;
}
}
block_46:
{
uint8_t x_44; 
x_44 = l_Lean_Exception_isInterrupt(x_42);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isRuntime(x_42);
x_30 = x_43;
x_31 = x_42;
x_32 = x_45;
goto block_41;
}
else
{
x_30 = x_43;
x_31 = x_42;
x_32 = x_44;
goto block_41;
}
}
block_74:
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_LocalDecl_toExpr(x_47);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_53 = l_Lean_MVarId_assert(x_2, x_50, x_51, x_52, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_28);
x_56 = l_Lean_Meta_Split_splitMatch(x_54, x_28, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_box(0);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_60 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1(x_49, x_57, x_59, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
if (lean_is_scalar(x_29)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_29;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
if (lean_is_scalar(x_29)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_29;
}
lean_ctor_set(x_66, 0, x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_29);
x_68 = lean_ctor_get(x_60, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_60, 1);
lean_inc(x_69);
lean_dec_ref(x_60);
x_42 = x_68;
x_43 = x_69;
goto block_46;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_29);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
lean_dec_ref(x_56);
x_42 = x_70;
x_43 = x_71;
goto block_46;
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_29);
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec_ref(x_53);
x_42 = x_72;
x_43 = x_73;
goto block_46;
}
}
block_81:
{
if (x_76 == 0)
{
lean_object* x_78; 
lean_dec_ref(x_75);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_2);
x_78 = l_Lean_Meta_Split_throwDiscrGenError___redArg(x_28, x_4, x_5, x_6, x_7, x_77);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 2);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 3);
lean_inc_ref(x_80);
x_47 = x_75;
x_48 = x_77;
x_49 = x_76;
x_50 = x_79;
x_51 = x_80;
goto block_74;
}
}
block_91:
{
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec_ref(x_83);
x_86 = lean_unbox(x_84);
lean_dec(x_84);
x_75 = x_82;
x_76 = x_86;
x_77 = x_85;
goto block_81;
}
else
{
uint8_t x_87; 
lean_dec_ref(x_82);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_167:
{
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_15);
x_93 = l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0;
lean_inc(x_3);
x_94 = lean_array_push(x_93, x_3);
x_95 = lean_box(x_92);
lean_inc(x_28);
lean_inc(x_2);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(x_96, 0, x_2);
lean_closure_set(x_96, 1, x_94);
lean_closure_set(x_96, 2, x_95);
lean_closure_set(x_96, 3, x_28);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_97 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_96, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
lean_inc_ref(x_4);
lean_inc(x_3);
x_100 = l_Lean_FVarId_getDecl___redArg(x_3, x_4, x_6, x_7, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec_ref(x_100);
lean_inc(x_2);
x_103 = l_Lean_MVarId_getType(x_2, x_4, x_5, x_6, x_7, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = l_Lean_LocalDecl_isLet(x_101, x_92);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_inc(x_3);
x_107 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_104, x_3, x_5, x_105);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec_ref(x_107);
lean_inc_ref(x_4);
x_111 = l_Lean_FVarId_hasForwardDeps(x_3, x_4, x_5, x_6, x_7, x_110);
x_82 = x_101;
x_83 = x_111;
goto block_91;
}
else
{
lean_dec(x_3);
x_82 = x_101;
x_83 = x_107;
goto block_91;
}
}
else
{
lean_dec(x_104);
lean_dec(x_3);
x_75 = x_101;
x_76 = x_106;
x_77 = x_105;
goto block_81;
}
}
else
{
uint8_t x_112; 
lean_dec(x_101);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_103);
if (x_112 == 0)
{
return x_103;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_103, 0);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_103);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_100);
if (x_116 == 0)
{
return x_100;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_100, 0);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_100);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_dec(x_98);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_97;
}
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_97;
}
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_120 = lean_box(0);
x_121 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_3, x_120, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
lean_dec(x_15);
x_123 = !lean_is_exclusive(x_121);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 0);
lean_dec(x_124);
x_125 = lean_box(0);
lean_ctor_set(x_121, 0, x_125);
return x_121;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_dec(x_121);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_122);
if (x_129 == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_121);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_122, 0);
x_132 = lean_ctor_get(x_121, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_131, 0);
x_135 = lean_ctor_get(x_131, 1);
x_136 = lean_box(0);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_136);
lean_ctor_set(x_131, 0, x_135);
if (lean_is_scalar(x_15)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_15;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_131);
lean_ctor_set(x_122, 0, x_137);
return x_121;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_131, 0);
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_131);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_15)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_15;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_138);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set(x_122, 0, x_142);
return x_121;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_122, 0);
x_144 = lean_ctor_get(x_121, 1);
lean_inc(x_144);
lean_dec(x_121);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_147 = x_143;
} else {
 lean_dec_ref(x_143);
 x_147 = lean_box(0);
}
x_148 = lean_box(0);
if (lean_is_scalar(x_147)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_147;
 lean_ctor_set_tag(x_149, 1);
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_15)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_15;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_145);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_122, 0, x_150);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_122);
lean_ctor_set(x_151, 1, x_144);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_122, 0);
lean_inc(x_152);
lean_dec(x_122);
x_153 = lean_ctor_get(x_121, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_154 = x_121;
} else {
 lean_dec_ref(x_121);
 x_154 = lean_box(0);
}
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_157 = x_152;
} else {
 lean_dec_ref(x_152);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_157;
 lean_ctor_set_tag(x_159, 1);
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
if (lean_is_scalar(x_15)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_15;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_155);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_154)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_154;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_153);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_15);
x_163 = !lean_is_exclusive(x_121);
if (x_163 == 0)
{
return x_121;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_121, 0);
x_165 = lean_ctor_get(x_121, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_121);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_18);
if (x_170 == 0)
{
return x_18;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_18, 0);
x_172 = lean_ctor_get(x_18, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_18);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_174 = !lean_is_exclusive(x_9);
if (x_174 == 0)
{
return x_9;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_9, 0);
x_176 = lean_ctor_get(x_9, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_9);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lam__1), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1), 8, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_splitLocalDecl_x3f___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_2 = l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6717_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(6717u);
x_2 = l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6717_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_3 = 0;
x_4 = l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6717_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_8 = l_Lean_registerTraceClass(x_7, x_3, x_4, x_6);
return x_8;
}
else
{
return x_5;
}
}
}
lean_object* initialize_Lean_Meta_Match_MatcherApp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Match_MatcherApp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Generalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0 = _init_l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0);
l_Lean_Meta_Split_simpMatch_pre___closed__0 = _init_l_Lean_Meta_Split_simpMatch_pre___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch_pre___closed__0);
l_Lean_Meta_Split_simpMatch___lam__1___closed__0 = _init_l_Lean_Meta_Split_simpMatch___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___lam__1___closed__0);
l_Lean_Meta_Split_simpMatch___closed__0 = _init_l_Lean_Meta_Split_simpMatch___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__0);
l_Lean_Meta_Split_simpMatch___closed__1 = _init_l_Lean_Meta_Split_simpMatch___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__1);
l_Lean_Meta_Split_simpMatch___closed__2 = _init_l_Lean_Meta_Split_simpMatch___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__2);
l_Lean_Meta_Split_simpMatch___closed__3 = _init_l_Lean_Meta_Split_simpMatch___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__3);
l_Lean_Meta_Split_simpMatch___closed__4 = _init_l_Lean_Meta_Split_simpMatch___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__4);
l_Lean_Meta_Split_simpMatch___closed__5 = _init_l_Lean_Meta_Split_simpMatch___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__5);
l_Lean_Meta_Split_simpMatch___closed__6 = _init_l_Lean_Meta_Split_simpMatch___closed__6();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__6);
l_Lean_Meta_Split_simpMatch___closed__7 = _init_l_Lean_Meta_Split_simpMatch___closed__7();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__7);
l_Lean_Meta_Split_simpMatch___closed__8 = _init_l_Lean_Meta_Split_simpMatch___closed__8();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__8);
l_Lean_Meta_Split_simpMatch___closed__9 = _init_l_Lean_Meta_Split_simpMatch___closed__9();
lean_mark_persistent(l_Lean_Meta_Split_simpMatch___closed__9);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1();
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0);
l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_881_ = _init_l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_881_();
lean_mark_persistent(l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_881_);
l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_881_ = _init_l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_881_();
lean_mark_persistent(l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_881_);
if (builtin) {res = l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_881_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Split_discrGenExId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Split_discrGenExId);
lean_dec_ref(res);
}l_Lean_Meta_Split_isDiscrGenException___closed__0 = _init_l_Lean_Meta_Split_isDiscrGenException___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_isDiscrGenException___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__5);
l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__0 = _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__0();
lean_mark_persistent(l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__0);
l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1 = _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1();
lean_mark_persistent(l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1);
l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2 = _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2();
lean_mark_persistent(l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2);
l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3 = _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3();
lean_mark_persistent(l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3);
l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4 = _init_l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4();
lean_mark_persistent(l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__1);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2);
l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3);
l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0 = _init_l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0);
l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1 = _init_l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1);
l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2 = _init_l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2();
lean_mark_persistent(l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__2);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__6);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__7);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8);
l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9 = _init_l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0);
l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1 = _init_l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1();
lean_mark_persistent(l_Std_PRange_RangeIterator_instIteratorLoop_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1);
l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0 = _init_l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0();
lean_mark_persistent(l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__3 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__3);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5);
l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1 = _init_l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___boxed__const__1);
l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__0 = _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__0();
lean_mark_persistent(l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__0);
l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1 = _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1();
lean_mark_persistent(l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1);
l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__2 = _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__2();
lean_mark_persistent(l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__2);
l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3 = _init_l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3();
lean_mark_persistent(l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0 = _init_l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0);
l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__0 = _init_l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__0);
l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___closed__0 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__0);
l_Lean_Meta_Split_applyMatchSplitter___closed__1 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__1);
l_Lean_Meta_Split_applyMatchSplitter___closed__2 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__2);
l_Lean_Meta_Split_applyMatchSplitter___closed__3 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__3);
l_Lean_Meta_Split_applyMatchSplitter___closed__4 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__4();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__4);
l_Lean_Meta_Split_applyMatchSplitter___closed__5 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__5();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__5);
l_Lean_Meta_Split_applyMatchSplitter___closed__6 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__6();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__6);
l_Lean_Meta_Split_applyMatchSplitter___closed__7 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__7();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__7);
l_Lean_Meta_Split_applyMatchSplitter___closed__8 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__8();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__8);
l_Lean_Meta_Split_applyMatchSplitter___closed__9 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__9();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__9);
l_Lean_Meta_Split_applyMatchSplitter___closed__10 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__10();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__10);
l_Lean_Meta_Split_applyMatchSplitter___closed__11 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__11();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__11);
l_Lean_Meta_Split_applyMatchSplitter___closed__12 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__12();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__12);
l_Lean_Meta_Split_applyMatchSplitter___closed__13 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__13();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__13);
l_Lean_Meta_Split_applyMatchSplitter___closed__14 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__14();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__14);
l_Lean_Meta_Split_applyMatchSplitter___closed__15 = _init_l_Lean_Meta_Split_applyMatchSplitter___closed__15();
lean_mark_persistent(l_Lean_Meta_Split_applyMatchSplitter___closed__15);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__2);
l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3 = _init_l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3);
l_Lean_Meta_Split_splitMatch___lam__0___closed__0 = _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lam__0___closed__0);
l_Lean_Meta_Split_splitMatch___lam__0___closed__1 = _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lam__0___closed__1);
l_Lean_Meta_Split_splitMatch___lam__0___closed__2 = _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lam__0___closed__2);
l_Lean_Meta_Split_splitMatch___lam__0___closed__3 = _init_l_Lean_Meta_Split_splitMatch___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_Split_splitMatch___lam__0___closed__3);
l_Lean_Meta_splitTarget_x3f_go___closed__0 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__0();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__0);
l_Lean_Meta_splitTarget_x3f_go___closed__1 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__1);
l_Lean_Meta_splitTarget_x3f_go___closed__2 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__2();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__2);
l_Lean_Meta_splitTarget_x3f_go___closed__3 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__3();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__3);
l_Lean_Meta_splitTarget_x3f_go___closed__4 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__4();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__4);
l_Lean_Meta_splitTarget_x3f_go___closed__5 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__5();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__5);
l_Lean_Meta_splitTarget_x3f_go___closed__6 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__6();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__6);
l_Lean_Meta_splitTarget_x3f_go___closed__7 = _init_l_Lean_Meta_splitTarget_x3f_go___closed__7();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f_go___closed__7);
l_Lean_Meta_splitTarget_x3f___lam__0___closed__0 = _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lam__0___closed__0);
l_Lean_Meta_splitTarget_x3f___lam__0___closed__1 = _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lam__0___closed__1);
l_Lean_Meta_splitTarget_x3f___lam__0___closed__2 = _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lam__0___closed__2);
l_Lean_Meta_splitTarget_x3f___lam__0___closed__3 = _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lam__0___closed__3);
l_Lean_Meta_splitTarget_x3f___lam__0___closed__4 = _init_l_Lean_Meta_splitTarget_x3f___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_splitTarget_x3f___lam__0___closed__4);
l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0 = _init_l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6717_);
l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6717_ = _init_l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6717_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6717_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6717_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
