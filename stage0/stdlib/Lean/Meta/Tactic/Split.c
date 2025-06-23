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
static lean_object* l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6655_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_880_(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__5;
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__1;
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__0;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_introNCore_spec__4(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__13;
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
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6655_;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6655_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__4;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2;
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0___closed__0;
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3;
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__0;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelParams_visitExpr_spec__1___redArg(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_delabDelayedAssignedMVar_spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__4;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__3;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__7;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___boxed(lean_object**);
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
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelParams_visitExpr_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
static lean_object* l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_880_;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__4;
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6655_;
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__3;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_splitIfTarget_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0;
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6655_;
extern lean_object* l_Lean_instInhabitedExpr;
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
static lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0;
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__4;
static lean_object* l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_880_;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6655_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isIte(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_;
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__1;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_x3f(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6655_;
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatchTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__8;
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6655_;
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6655_(lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__0;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___boxed(lean_object**);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findSplit_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6655_;
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
static lean_object* l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6655_;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Split_simpMatch___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_hasForwardDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6655_;
static lean_object* l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6655_;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6655_;
lean_object* l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6655_;
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
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lean_Meta_Split_splitMatch___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__0;
static lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_Split_isDiscrGenException(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6655_;
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
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__2;
static lean_object* l_Lean_Meta_Split_mkDiscrGenErrorMsg___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lean_Meta_splitTarget_x3f_go___closed__0;
static lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__0;
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
lean_dec(x_4);
x_7 = l_Lean_Meta_Simp_neutralConfig;
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_9 = lean_box(0);
x_10 = lean_box(1);
x_11 = lean_box(2);
x_12 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2, x_12);
x_13 = lean_unbox(x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 1, x_13);
x_14 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 2, x_14);
x_15 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 3, x_15);
x_16 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 4, x_16);
x_17 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 5, x_17);
x_18 = lean_unbox(x_11);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_18);
x_19 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_19);
x_20 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 8, x_20);
x_21 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 9, x_21);
x_22 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 10, x_22);
x_23 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 11, x_23);
x_24 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 12, x_24);
x_25 = lean_unbox(x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 13, x_25);
x_26 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 14, x_26);
x_27 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 15, x_27);
x_28 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 16, x_28);
x_29 = lean_unbox(x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 17, x_29);
x_30 = lean_unbox(x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 18, x_30);
x_31 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 19, x_31);
x_32 = lean_unbox(x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 20, x_32);
x_33 = lean_unbox(x_10);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 21, x_33);
x_34 = lean_unbox(x_9);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 22, x_34);
x_35 = l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0;
x_36 = l_Lean_Meta_Simp_mkContext___redArg(x_7, x_35, x_5, x_1, x_2, x_6);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_box(0);
x_40 = lean_box(1);
x_41 = lean_box(2);
x_42 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_38);
x_43 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_43);
x_44 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 1, x_44);
x_45 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 2, x_45);
x_46 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 3, x_46);
x_47 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 4, x_47);
x_48 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 5, x_48);
x_49 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 6, x_49);
x_50 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 7, x_50);
x_51 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 8, x_51);
x_52 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 9, x_52);
x_53 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 10, x_53);
x_54 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 11, x_54);
x_55 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 12, x_55);
x_56 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 13, x_56);
x_57 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 14, x_57);
x_58 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 15, x_58);
x_59 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_59);
x_60 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 17, x_60);
x_61 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 18, x_61);
x_62 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 19, x_62);
x_63 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 20, x_63);
x_64 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 21, x_64);
x_65 = lean_unbox(x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 22, x_65);
x_66 = l_Lean_Meta_Split_getSimpMatchContext___redArg___closed__0;
x_67 = l_Lean_Meta_Simp_mkContext___redArg(x_42, x_66, x_5, x_1, x_2, x_6);
return x_67;
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_getSimpMatchContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Split_getSimpMatchContext(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_7);
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
lean_inc(x_12);
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
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
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
lean_dec(x_20);
x_23 = l_Lean_Expr_getAppFn(x_1);
x_24 = l_Lean_Expr_constName_x21(x_23);
lean_dec(x_23);
x_25 = l_Lean_Meta_Simp_simpMatchCore(x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isMatcherApp___at___Lean_Meta_Split_simpMatch_pre_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_box(1);
x_12 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
lean_inc(x_2);
x_9 = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(x_8, x_2, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_Split_getSimpMatchContext___redArg(x_2, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__0___boxed), 9, 0);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__1___boxed), 9, 0);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_Split_simpMatch___lam__2___boxed), 9, 0);
x_18 = l_Lean_Meta_Split_simpMatch___closed__8;
x_19 = l_Lean_Meta_Split_simpMatch___closed__9;
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_10);
x_22 = lean_unbox(x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_22);
x_23 = l_Lean_Meta_Simp_main(x_1, x_13, x_18, x_21, x_2, x_3, x_4, x_5, x_14);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Split_simpMatch___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Split_simpMatch___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_7);
x_10 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_8, x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
x_13 = l_Lean_Meta_Split_simpMatch(x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_applySimpResultToTarget(x_1, x_11, x_14, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_11);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(2);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
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
lean_dec(x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_28 = l_Lean_Meta_isRflTheorem(x_2, x_9, x_10, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_7, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; 
x_36 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
x_37 = lean_box(0);
lean_inc(x_2);
x_38 = l_Lean_Expr_const___override(x_2, x_37);
x_39 = lean_unsigned_to_nat(1000u);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_22);
x_42 = lean_unbox(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1 + 1, x_42);
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_39);
lean_ctor_set(x_43, 4, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_22);
x_44 = lean_unbox(x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_44);
x_45 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_45);
x_46 = lean_box(2);
x_47 = lean_unbox(x_46);
lean_ctor_set_uint8(x_29, 9, x_47);
x_48 = 2;
x_49 = lean_uint64_shift_right(x_33, x_48);
x_50 = lean_uint64_shift_left(x_49, x_48);
x_51 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_52 = lean_uint64_lor(x_50, x_51);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_52);
x_53 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_43, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_12 = x_54;
x_13 = x_55;
goto block_21;
}
else
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_12 = x_56;
x_13 = x_57;
goto block_21;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_53);
if (x_58 == 0)
{
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
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
uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; lean_object* x_97; 
x_62 = lean_ctor_get_uint8(x_29, 0);
x_63 = lean_ctor_get_uint8(x_29, 1);
x_64 = lean_ctor_get_uint8(x_29, 2);
x_65 = lean_ctor_get_uint8(x_29, 3);
x_66 = lean_ctor_get_uint8(x_29, 4);
x_67 = lean_ctor_get_uint8(x_29, 5);
x_68 = lean_ctor_get_uint8(x_29, 6);
x_69 = lean_ctor_get_uint8(x_29, 7);
x_70 = lean_ctor_get_uint8(x_29, 8);
x_71 = lean_ctor_get_uint8(x_29, 10);
x_72 = lean_ctor_get_uint8(x_29, 11);
x_73 = lean_ctor_get_uint8(x_29, 12);
x_74 = lean_ctor_get_uint8(x_29, 13);
x_75 = lean_ctor_get_uint8(x_29, 14);
x_76 = lean_ctor_get_uint8(x_29, 15);
x_77 = lean_ctor_get_uint8(x_29, 16);
x_78 = lean_ctor_get_uint8(x_29, 17);
lean_dec(x_29);
x_79 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
x_80 = lean_box(0);
lean_inc(x_2);
x_81 = l_Lean_Expr_const___override(x_2, x_80);
x_82 = lean_unsigned_to_nat(1000u);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_84, 0, x_2);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_22);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1 + 1, x_85);
x_86 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set(x_86, 4, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*5, x_22);
x_87 = lean_unbox(x_83);
lean_ctor_set_uint8(x_86, sizeof(void*)*5 + 1, x_87);
x_88 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_86, sizeof(void*)*5 + 2, x_88);
x_89 = lean_box(2);
x_90 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_90, 0, x_62);
lean_ctor_set_uint8(x_90, 1, x_63);
lean_ctor_set_uint8(x_90, 2, x_64);
lean_ctor_set_uint8(x_90, 3, x_65);
lean_ctor_set_uint8(x_90, 4, x_66);
lean_ctor_set_uint8(x_90, 5, x_67);
lean_ctor_set_uint8(x_90, 6, x_68);
lean_ctor_set_uint8(x_90, 7, x_69);
lean_ctor_set_uint8(x_90, 8, x_70);
x_91 = lean_unbox(x_89);
lean_ctor_set_uint8(x_90, 9, x_91);
lean_ctor_set_uint8(x_90, 10, x_71);
lean_ctor_set_uint8(x_90, 11, x_72);
lean_ctor_set_uint8(x_90, 12, x_73);
lean_ctor_set_uint8(x_90, 13, x_74);
lean_ctor_set_uint8(x_90, 14, x_75);
lean_ctor_set_uint8(x_90, 15, x_76);
lean_ctor_set_uint8(x_90, 16, x_77);
lean_ctor_set_uint8(x_90, 17, x_78);
x_92 = 2;
x_93 = lean_uint64_shift_right(x_33, x_92);
x_94 = lean_uint64_shift_left(x_93, x_92);
x_95 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_96 = lean_uint64_lor(x_94, x_95);
lean_ctor_set(x_7, 0, x_90);
lean_ctor_set_uint64(x_7, sizeof(void*)*7, x_96);
x_97 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_86, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_12 = x_98;
x_13 = x_99;
goto block_21;
}
else
{
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_12 = x_100;
x_13 = x_101;
goto block_21;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_104 = x_97;
} else {
 lean_dec_ref(x_97);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
else
{
uint64_t x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; lean_object* x_152; lean_object* x_153; 
x_106 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_107 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_108 = lean_ctor_get(x_7, 1);
x_109 = lean_ctor_get(x_7, 2);
x_110 = lean_ctor_get(x_7, 3);
x_111 = lean_ctor_get(x_7, 4);
x_112 = lean_ctor_get(x_7, 5);
x_113 = lean_ctor_get(x_7, 6);
x_114 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_115 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_7);
x_116 = lean_ctor_get_uint8(x_29, 0);
x_117 = lean_ctor_get_uint8(x_29, 1);
x_118 = lean_ctor_get_uint8(x_29, 2);
x_119 = lean_ctor_get_uint8(x_29, 3);
x_120 = lean_ctor_get_uint8(x_29, 4);
x_121 = lean_ctor_get_uint8(x_29, 5);
x_122 = lean_ctor_get_uint8(x_29, 6);
x_123 = lean_ctor_get_uint8(x_29, 7);
x_124 = lean_ctor_get_uint8(x_29, 8);
x_125 = lean_ctor_get_uint8(x_29, 10);
x_126 = lean_ctor_get_uint8(x_29, 11);
x_127 = lean_ctor_get_uint8(x_29, 12);
x_128 = lean_ctor_get_uint8(x_29, 13);
x_129 = lean_ctor_get_uint8(x_29, 14);
x_130 = lean_ctor_get_uint8(x_29, 15);
x_131 = lean_ctor_get_uint8(x_29, 16);
x_132 = lean_ctor_get_uint8(x_29, 17);
if (lean_is_exclusive(x_29)) {
 x_133 = x_29;
} else {
 lean_dec_ref(x_29);
 x_133 = lean_box(0);
}
x_134 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__0;
x_135 = lean_box(0);
lean_inc(x_2);
x_136 = l_Lean_Expr_const___override(x_2, x_135);
x_137 = lean_unsigned_to_nat(1000u);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_139, 0, x_2);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_22);
x_140 = lean_unbox(x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*1 + 1, x_140);
x_141 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_134);
lean_ctor_set(x_141, 2, x_136);
lean_ctor_set(x_141, 3, x_137);
lean_ctor_set(x_141, 4, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*5, x_22);
x_142 = lean_unbox(x_138);
lean_ctor_set_uint8(x_141, sizeof(void*)*5 + 1, x_142);
x_143 = lean_unbox(x_30);
lean_dec(x_30);
lean_ctor_set_uint8(x_141, sizeof(void*)*5 + 2, x_143);
x_144 = lean_box(2);
if (lean_is_scalar(x_133)) {
 x_145 = lean_alloc_ctor(0, 0, 18);
} else {
 x_145 = x_133;
}
lean_ctor_set_uint8(x_145, 0, x_116);
lean_ctor_set_uint8(x_145, 1, x_117);
lean_ctor_set_uint8(x_145, 2, x_118);
lean_ctor_set_uint8(x_145, 3, x_119);
lean_ctor_set_uint8(x_145, 4, x_120);
lean_ctor_set_uint8(x_145, 5, x_121);
lean_ctor_set_uint8(x_145, 6, x_122);
lean_ctor_set_uint8(x_145, 7, x_123);
lean_ctor_set_uint8(x_145, 8, x_124);
x_146 = lean_unbox(x_144);
lean_ctor_set_uint8(x_145, 9, x_146);
lean_ctor_set_uint8(x_145, 10, x_125);
lean_ctor_set_uint8(x_145, 11, x_126);
lean_ctor_set_uint8(x_145, 12, x_127);
lean_ctor_set_uint8(x_145, 13, x_128);
lean_ctor_set_uint8(x_145, 14, x_129);
lean_ctor_set_uint8(x_145, 15, x_130);
lean_ctor_set_uint8(x_145, 16, x_131);
lean_ctor_set_uint8(x_145, 17, x_132);
x_147 = 2;
x_148 = lean_uint64_shift_right(x_106, x_147);
x_149 = lean_uint64_shift_left(x_148, x_147);
x_150 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___closed__1;
x_151 = lean_uint64_lor(x_149, x_150);
x_152 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_108);
lean_ctor_set(x_152, 2, x_109);
lean_ctor_set(x_152, 3, x_110);
lean_ctor_set(x_152, 4, x_111);
lean_ctor_set(x_152, 5, x_112);
lean_ctor_set(x_152, 6, x_113);
lean_ctor_set_uint64(x_152, sizeof(void*)*7, x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 8, x_107);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 9, x_114);
lean_ctor_set_uint8(x_152, sizeof(void*)*7 + 10, x_115);
x_153 = l_Lean_Meta_Simp_tryTheorem_x3f(x_3, x_141, x_4, x_5, x_6, x_152, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_12 = x_154;
x_13 = x_155;
goto block_21;
}
else
{
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_12 = x_156;
x_13 = x_157;
goto block_21;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_160 = x_153;
} else {
 lean_dec_ref(x_153);
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
}
else
{
uint8_t x_162; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_28);
if (x_162 == 0)
{
return x_28;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_28, 0);
x_164 = lean_ctor_get(x_28, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_28);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_166 = !lean_is_exclusive(x_25);
if (x_166 == 0)
{
lean_object* x_167; uint8_t x_168; 
x_167 = lean_ctor_get(x_25, 0);
lean_dec(x_167);
x_168 = !lean_is_exclusive(x_26);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_26, 0);
x_170 = lean_box(0);
x_171 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*2, x_22);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 0, x_171);
return x_25;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_26, 0);
lean_inc(x_172);
lean_dec(x_26);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
lean_ctor_set_uint8(x_174, sizeof(void*)*2, x_22);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_25, 0, x_175);
return x_25;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_25, 1);
lean_inc(x_176);
lean_dec(x_25);
x_177 = lean_ctor_get(x_26, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_178 = x_26;
} else {
 lean_dec_ref(x_26);
 x_178 = lean_box(0);
}
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*2, x_22);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 1, 0);
} else {
 x_181 = x_178;
 lean_ctor_set_tag(x_181, 0);
}
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_176);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_183 = !lean_is_exclusive(x_25);
if (x_183 == 0)
{
return x_25;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_25, 0);
x_185 = lean_ctor_get(x_25, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_25);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
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
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
lean_inc(x_4);
x_11 = l_Lean_Meta_SplitIf_mkDischarge_x3f___redArg(x_10, x_4, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Split_getSimpMatchContext___redArg(x_4, x_7, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__0;
x_18 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__1;
x_19 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore___closed__2;
x_20 = l_Lean_Meta_Split_simpMatch___closed__8;
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchCore_pre___boxed), 11, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_12);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*5, x_24);
x_25 = l_Lean_Meta_Simp_main(x_3, x_15, x_20, x_23, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
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
lean_dec(x_9);
x_12 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_10, x_5, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
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
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_19, x_4, x_5, x_6, x_7, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = lean_infer_type(x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_isEq(x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l_Lean_Meta_mkHEqRefl(x_7, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Meta_mkEqRefl(x_7, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_16);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_1, x_4);
x_21 = lean_array_get(x_19, x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_22 = l_Lean_Meta_mkEqHEq(x_20, x_21, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
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
lean_dec(x_20);
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
static lean_object* _init_l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_880_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("discrGeneralizationFailure", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_880_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_880_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_880_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_880_;
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
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Meta_Split_isDiscrGenException___closed__0;
x_7 = lean_nat_dec_eq(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_isDiscrGenException___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Split_isDiscrGenException(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Lean_Meta_mkHEqTrans(x_1, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l_Lean_Meta_mkEqTrans(x_1, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_apply_7(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_array_get(x_23, x_1, x_4);
lean_inc(x_7);
x_25 = l_Lean_Meta_getFVarLocalDecl___redArg(x_24, x_7, x_9, x_10, x_11);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_array_get(x_23, x_3, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_28);
x_29 = lean_infer_type(x_28, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_50; lean_object* x_51; lean_object* x_64; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_28);
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
lean_inc(x_64);
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
lean_dec(x_33);
lean_dec(x_32);
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
lean_dec(x_33);
lean_dec(x_32);
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
lean_dec(x_33);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_44 = l_Lean_Meta_mkHEq(x_42, x_43, x_34, x_35, x_36, x_37, x_31);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_26, 2);
lean_inc(x_47);
lean_dec(x_26);
x_48 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_47, x_45, x_32, x_34, x_35, x_36, x_37, x_46);
return x_48;
}
else
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
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
lean_dec(x_50);
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
lean_dec(x_50);
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
lean_dec(x_32);
x_56 = l_Lean_Expr_appArg_x21(x_30);
lean_dec(x_30);
x_57 = l_Lean_Expr_appArg_x21(x_51);
lean_dec(x_51);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_58 = l_Lean_Meta_mkEq(x_56, x_57, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_26, 2);
lean_inc(x_61);
lean_dec(x_26);
x_62 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Simp_Arith_withAbstractAtoms_go_spec__0___redArg(x_61, x_59, x_50, x_7, x_8, x_9, x_10, x_60);
return x_62;
}
else
{
lean_dec(x_50);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_58;
}
}
}
}
}
else
{
lean_dec(x_28);
lean_dec(x_26);
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
return x_29;
}
}
else
{
uint8_t x_65; 
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
lean_dec(x_11);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
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
lean_dec(x_11);
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
lean_dec(x_1);
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
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_13);
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
lean_inc(x_31);
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
lean_inc(x_48);
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
lean_inc(x_66);
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
lean_inc(x_66);
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
lean_inc(x_85);
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
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
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
lean_inc(x_101);
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
lean_inc(x_121);
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
lean_inc(x_121);
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
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
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
lean_inc(x_139);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
lean_dec(x_13);
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
lean_dec(x_11);
x_19 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0(x_19, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_1 = x_10;
x_7 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_14, 4);
lean_inc(x_16);
lean_dec(x_14);
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
lean_dec(x_12);
x_20 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l_panic___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__0(x_20, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1_spec__1___redArg(x_11, x_3, x_4, x_5, x_6, x_7, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_47; uint8_t x_48; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_47 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_9, x_6, x_7);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_free_object(x_47);
x_52 = lean_st_ref_get(x_6, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
if (x_2 == 0)
{
lean_dec(x_53);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
goto block_143;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_53, 0);
lean_inc(x_144);
lean_dec(x_53);
lean_inc(x_9);
x_145 = l_Lean_isCasesOnRecursor(x_144, x_9);
if (x_145 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
goto block_143;
}
else
{
if (lean_obj_tag(x_9) == 0)
{
x_55 = x_9;
goto block_140;
}
else
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_9, 0);
lean_inc(x_146);
x_55 = x_146;
goto block_140;
}
}
}
block_140:
{
lean_object* x_56; 
x_56 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_55, x_3, x_4, x_5, x_6, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 5)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_ctor_get(x_56, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 4);
lean_inc(x_65);
x_66 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
x_67 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_67);
x_68 = lean_mk_array(x_67, x_66);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_67, x_69);
lean_dec(x_67);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_68, x_70);
x_72 = lean_nat_add(x_63, x_69);
x_73 = lean_nat_add(x_72, x_64);
x_74 = lean_nat_add(x_73, x_69);
lean_dec(x_73);
x_75 = l_Lean_InductiveVal_numCtors(x_58);
lean_dec(x_58);
x_76 = lean_nat_add(x_74, x_75);
lean_dec(x_75);
x_77 = lean_array_get_size(x_71);
x_78 = lean_nat_dec_le(x_76, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_box(0);
lean_ctor_set(x_56, 0, x_79);
return x_56;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_free_object(x_56);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
lean_dec(x_62);
x_81 = lean_unsigned_to_nat(0u);
lean_inc(x_63);
lean_inc(x_71);
x_82 = l_Array_toSubarray___redArg(x_71, x_81, x_63);
x_83 = lean_array_get(x_51, x_71, x_63);
lean_dec(x_63);
lean_inc(x_74);
lean_inc(x_71);
x_84 = l_Array_toSubarray___redArg(x_71, x_72, x_74);
x_85 = lean_nat_add(x_64, x_69);
lean_dec(x_64);
x_86 = lean_box(0);
x_87 = lean_mk_array(x_85, x_86);
lean_inc(x_76);
lean_inc(x_71);
x_88 = l_Array_toSubarray___redArg(x_71, x_74, x_76);
x_89 = l_Array_toSubarray___redArg(x_71, x_76, x_77);
x_90 = l_List_lengthTR___redArg(x_80);
lean_dec(x_80);
x_91 = l_List_lengthTR___redArg(x_10);
x_92 = lean_nat_dec_eq(x_90, x_91);
lean_dec(x_91);
lean_dec(x_90);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1;
x_11 = x_87;
x_12 = x_84;
x_13 = x_83;
x_14 = x_88;
x_15 = x_65;
x_16 = x_81;
x_17 = x_82;
x_18 = x_60;
x_19 = x_89;
x_20 = x_93;
goto block_46;
}
else
{
lean_object* x_94; 
x_94 = lean_box(0);
x_11 = x_87;
x_12 = x_84;
x_13 = x_83;
x_14 = x_88;
x_15 = x_65;
x_16 = x_81;
x_17 = x_82;
x_18 = x_60;
x_19 = x_89;
x_20 = x_94;
goto block_46;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_95 = lean_ctor_get(x_56, 1);
lean_inc(x_95);
lean_dec(x_56);
x_96 = lean_ctor_get(x_58, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_58, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_58, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_58, 4);
lean_inc(x_99);
x_100 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
x_101 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_101);
x_102 = lean_mk_array(x_101, x_100);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_sub(x_101, x_103);
lean_dec(x_101);
x_105 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_102, x_104);
x_106 = lean_nat_add(x_97, x_103);
x_107 = lean_nat_add(x_106, x_98);
x_108 = lean_nat_add(x_107, x_103);
lean_dec(x_107);
x_109 = l_Lean_InductiveVal_numCtors(x_58);
lean_dec(x_58);
x_110 = lean_nat_add(x_108, x_109);
lean_dec(x_109);
x_111 = lean_array_get_size(x_105);
x_112 = lean_nat_dec_le(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_115 = lean_ctor_get(x_96, 1);
lean_inc(x_115);
lean_dec(x_96);
x_116 = lean_unsigned_to_nat(0u);
lean_inc(x_97);
lean_inc(x_105);
x_117 = l_Array_toSubarray___redArg(x_105, x_116, x_97);
x_118 = lean_array_get(x_51, x_105, x_97);
lean_dec(x_97);
lean_inc(x_108);
lean_inc(x_105);
x_119 = l_Array_toSubarray___redArg(x_105, x_106, x_108);
x_120 = lean_nat_add(x_98, x_103);
lean_dec(x_98);
x_121 = lean_box(0);
x_122 = lean_mk_array(x_120, x_121);
lean_inc(x_110);
lean_inc(x_105);
x_123 = l_Array_toSubarray___redArg(x_105, x_108, x_110);
x_124 = l_Array_toSubarray___redArg(x_105, x_110, x_111);
x_125 = l_List_lengthTR___redArg(x_115);
lean_dec(x_115);
x_126 = l_List_lengthTR___redArg(x_10);
x_127 = lean_nat_dec_eq(x_125, x_126);
lean_dec(x_126);
lean_dec(x_125);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1;
x_11 = x_122;
x_12 = x_119;
x_13 = x_118;
x_14 = x_123;
x_15 = x_99;
x_16 = x_116;
x_17 = x_117;
x_18 = x_95;
x_19 = x_124;
x_20 = x_128;
goto block_46;
}
else
{
lean_object* x_129; 
x_129 = lean_box(0);
x_11 = x_122;
x_12 = x_119;
x_13 = x_118;
x_14 = x_123;
x_15 = x_99;
x_16 = x_116;
x_17 = x_117;
x_18 = x_95;
x_19 = x_124;
x_20 = x_129;
goto block_46;
}
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_56);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_56, 0);
lean_dec(x_131);
x_132 = lean_box(0);
lean_ctor_set(x_56, 0, x_132);
return x_56;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_56, 1);
lean_inc(x_133);
lean_dec(x_56);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_56);
if (x_136 == 0)
{
return x_56;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_56, 0);
x_138 = lean_ctor_get(x_56, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_56);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
block_143:
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
x_142 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(x_141, x_3, x_4, x_5, x_6, x_54);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_142;
}
}
else
{
uint8_t x_147; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_49);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_148 = lean_ctor_get(x_49, 0);
x_149 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
x_150 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_150);
x_151 = lean_mk_array(x_150, x_149);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_nat_sub(x_150, x_152);
lean_dec(x_150);
x_154 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_151, x_153);
x_155 = lean_array_get_size(x_154);
x_156 = l_Lean_Meta_Match_MatcherInfo_arity(x_148);
x_157 = lean_nat_dec_lt(x_155, x_156);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_158 = lean_ctor_get(x_148, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_148, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_148, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_148, 3);
lean_inc(x_161);
x_162 = lean_ctor_get(x_148, 4);
lean_inc(x_162);
x_163 = lean_array_mk(x_10);
x_164 = lean_unsigned_to_nat(0u);
lean_inc(x_158);
x_165 = l_Array_extract___redArg(x_154, x_164, x_158);
x_166 = lean_array_get(x_51, x_154, x_158);
x_167 = lean_nat_add(x_158, x_152);
lean_dec(x_158);
x_168 = lean_nat_add(x_167, x_159);
lean_dec(x_159);
lean_inc(x_168);
lean_inc(x_154);
x_169 = l_Array_toSubarray___redArg(x_154, x_167, x_168);
x_170 = l_Array_ofSubarray___redArg(x_169);
lean_dec(x_169);
x_171 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_148);
lean_dec(x_148);
x_172 = lean_nat_add(x_168, x_171);
lean_dec(x_171);
lean_inc(x_172);
lean_inc(x_154);
x_173 = l_Array_toSubarray___redArg(x_154, x_168, x_172);
x_174 = l_Array_ofSubarray___redArg(x_173);
lean_dec(x_173);
x_175 = l_Array_toSubarray___redArg(x_154, x_172, x_155);
x_176 = l_Array_ofSubarray___redArg(x_175);
lean_dec(x_175);
x_177 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_177, 0, x_9);
lean_ctor_set(x_177, 1, x_163);
lean_ctor_set(x_177, 2, x_161);
lean_ctor_set(x_177, 3, x_162);
lean_ctor_set(x_177, 4, x_165);
lean_ctor_set(x_177, 5, x_166);
lean_ctor_set(x_177, 6, x_170);
lean_ctor_set(x_177, 7, x_160);
lean_ctor_set(x_177, 8, x_174);
lean_ctor_set(x_177, 9, x_176);
lean_ctor_set(x_49, 0, x_177);
return x_47;
}
else
{
lean_object* x_178; 
lean_dec(x_155);
lean_dec(x_154);
lean_free_object(x_49);
lean_dec(x_148);
lean_dec(x_10);
lean_dec(x_9);
x_178 = lean_box(0);
lean_ctor_set(x_47, 0, x_178);
return x_47;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_49, 0);
lean_inc(x_179);
lean_dec(x_49);
x_180 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
x_181 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_181);
x_182 = lean_mk_array(x_181, x_180);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_nat_sub(x_181, x_183);
lean_dec(x_181);
x_185 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_182, x_184);
x_186 = lean_array_get_size(x_185);
x_187 = l_Lean_Meta_Match_MatcherInfo_arity(x_179);
x_188 = lean_nat_dec_lt(x_186, x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_189 = lean_ctor_get(x_179, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_179, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_179, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_179, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_179, 4);
lean_inc(x_193);
x_194 = lean_array_mk(x_10);
x_195 = lean_unsigned_to_nat(0u);
lean_inc(x_189);
x_196 = l_Array_extract___redArg(x_185, x_195, x_189);
x_197 = lean_array_get(x_51, x_185, x_189);
x_198 = lean_nat_add(x_189, x_183);
lean_dec(x_189);
x_199 = lean_nat_add(x_198, x_190);
lean_dec(x_190);
lean_inc(x_199);
lean_inc(x_185);
x_200 = l_Array_toSubarray___redArg(x_185, x_198, x_199);
x_201 = l_Array_ofSubarray___redArg(x_200);
lean_dec(x_200);
x_202 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_179);
lean_dec(x_179);
x_203 = lean_nat_add(x_199, x_202);
lean_dec(x_202);
lean_inc(x_203);
lean_inc(x_185);
x_204 = l_Array_toSubarray___redArg(x_185, x_199, x_203);
x_205 = l_Array_ofSubarray___redArg(x_204);
lean_dec(x_204);
x_206 = l_Array_toSubarray___redArg(x_185, x_203, x_186);
x_207 = l_Array_ofSubarray___redArg(x_206);
lean_dec(x_206);
x_208 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_208, 0, x_9);
lean_ctor_set(x_208, 1, x_194);
lean_ctor_set(x_208, 2, x_192);
lean_ctor_set(x_208, 3, x_193);
lean_ctor_set(x_208, 4, x_196);
lean_ctor_set(x_208, 5, x_197);
lean_ctor_set(x_208, 6, x_201);
lean_ctor_set(x_208, 7, x_191);
lean_ctor_set(x_208, 8, x_205);
lean_ctor_set(x_208, 9, x_207);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_47, 0, x_209);
return x_47;
}
else
{
lean_object* x_210; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_179);
lean_dec(x_10);
lean_dec(x_9);
x_210 = lean_box(0);
lean_ctor_set(x_47, 0, x_210);
return x_47;
}
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_47, 0);
x_212 = lean_ctor_get(x_47, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_47);
x_213 = l_Lean_instInhabitedExpr;
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_214 = lean_st_ref_get(x_6, x_212);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
if (x_2 == 0)
{
lean_dec(x_215);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
goto block_268;
}
else
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_215, 0);
lean_inc(x_269);
lean_dec(x_215);
lean_inc(x_9);
x_270 = l_Lean_isCasesOnRecursor(x_269, x_9);
if (x_270 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
goto block_268;
}
else
{
if (lean_obj_tag(x_9) == 0)
{
x_217 = x_9;
goto block_265;
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_9, 0);
lean_inc(x_271);
x_217 = x_271;
goto block_265;
}
}
}
block_265:
{
lean_object* x_218; 
x_218 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_217, x_3, x_4, x_5, x_6, x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_obj_tag(x_219) == 5)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_222 = x_218;
} else {
 lean_dec_ref(x_218);
 x_222 = lean_box(0);
}
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_220, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_220, 4);
lean_inc(x_226);
x_227 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
x_228 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_228);
x_229 = lean_mk_array(x_228, x_227);
x_230 = lean_unsigned_to_nat(1u);
x_231 = lean_nat_sub(x_228, x_230);
lean_dec(x_228);
x_232 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_229, x_231);
x_233 = lean_nat_add(x_224, x_230);
x_234 = lean_nat_add(x_233, x_225);
x_235 = lean_nat_add(x_234, x_230);
lean_dec(x_234);
x_236 = l_Lean_InductiveVal_numCtors(x_220);
lean_dec(x_220);
x_237 = lean_nat_add(x_235, x_236);
lean_dec(x_236);
x_238 = lean_array_get_size(x_232);
x_239 = lean_nat_dec_le(x_237, x_238);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_240 = lean_box(0);
if (lean_is_scalar(x_222)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_222;
}
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_221);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_dec(x_222);
x_242 = lean_ctor_get(x_223, 1);
lean_inc(x_242);
lean_dec(x_223);
x_243 = lean_unsigned_to_nat(0u);
lean_inc(x_224);
lean_inc(x_232);
x_244 = l_Array_toSubarray___redArg(x_232, x_243, x_224);
x_245 = lean_array_get(x_213, x_232, x_224);
lean_dec(x_224);
lean_inc(x_235);
lean_inc(x_232);
x_246 = l_Array_toSubarray___redArg(x_232, x_233, x_235);
x_247 = lean_nat_add(x_225, x_230);
lean_dec(x_225);
x_248 = lean_box(0);
x_249 = lean_mk_array(x_247, x_248);
lean_inc(x_237);
lean_inc(x_232);
x_250 = l_Array_toSubarray___redArg(x_232, x_235, x_237);
x_251 = l_Array_toSubarray___redArg(x_232, x_237, x_238);
x_252 = l_List_lengthTR___redArg(x_242);
lean_dec(x_242);
x_253 = l_List_lengthTR___redArg(x_10);
x_254 = lean_nat_dec_eq(x_252, x_253);
lean_dec(x_253);
lean_dec(x_252);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__1;
x_11 = x_249;
x_12 = x_246;
x_13 = x_245;
x_14 = x_250;
x_15 = x_226;
x_16 = x_243;
x_17 = x_244;
x_18 = x_221;
x_19 = x_251;
x_20 = x_255;
goto block_46;
}
else
{
lean_object* x_256; 
x_256 = lean_box(0);
x_11 = x_249;
x_12 = x_246;
x_13 = x_245;
x_14 = x_250;
x_15 = x_226;
x_16 = x_243;
x_17 = x_244;
x_18 = x_221;
x_19 = x_251;
x_20 = x_256;
goto block_46;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_219);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_257 = lean_ctor_get(x_218, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_258 = x_218;
} else {
 lean_dec_ref(x_218);
 x_258 = lean_box(0);
}
x_259 = lean_box(0);
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 2, 0);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_261 = lean_ctor_get(x_218, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_218, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_263 = x_218;
} else {
 lean_dec_ref(x_218);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 2, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_262);
return x_264;
}
}
block_268:
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_box(0);
x_267 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(x_266, x_3, x_4, x_5, x_6, x_216);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_267;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_272 = lean_ctor_get(x_211, 0);
lean_inc(x_272);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_273 = x_211;
} else {
 lean_dec_ref(x_211);
 x_273 = lean_box(0);
}
x_274 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___closed__0;
x_275 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_275);
x_276 = lean_mk_array(x_275, x_274);
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_nat_sub(x_275, x_277);
lean_dec(x_275);
x_279 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_276, x_278);
x_280 = lean_array_get_size(x_279);
x_281 = l_Lean_Meta_Match_MatcherInfo_arity(x_272);
x_282 = lean_nat_dec_lt(x_280, x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_283 = lean_ctor_get(x_272, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_272, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_272, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_272, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_272, 4);
lean_inc(x_287);
x_288 = lean_array_mk(x_10);
x_289 = lean_unsigned_to_nat(0u);
lean_inc(x_283);
x_290 = l_Array_extract___redArg(x_279, x_289, x_283);
x_291 = lean_array_get(x_213, x_279, x_283);
x_292 = lean_nat_add(x_283, x_277);
lean_dec(x_283);
x_293 = lean_nat_add(x_292, x_284);
lean_dec(x_284);
lean_inc(x_293);
lean_inc(x_279);
x_294 = l_Array_toSubarray___redArg(x_279, x_292, x_293);
x_295 = l_Array_ofSubarray___redArg(x_294);
lean_dec(x_294);
x_296 = l_Lean_Meta_Match_MatcherInfo_numAlts(x_272);
lean_dec(x_272);
x_297 = lean_nat_add(x_293, x_296);
lean_dec(x_296);
lean_inc(x_297);
lean_inc(x_279);
x_298 = l_Array_toSubarray___redArg(x_279, x_293, x_297);
x_299 = l_Array_ofSubarray___redArg(x_298);
lean_dec(x_298);
x_300 = l_Array_toSubarray___redArg(x_279, x_297, x_280);
x_301 = l_Array_ofSubarray___redArg(x_300);
lean_dec(x_300);
x_302 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_302, 0, x_9);
lean_ctor_set(x_302, 1, x_288);
lean_ctor_set(x_302, 2, x_286);
lean_ctor_set(x_302, 3, x_287);
lean_ctor_set(x_302, 4, x_290);
lean_ctor_set(x_302, 5, x_291);
lean_ctor_set(x_302, 6, x_295);
lean_ctor_set(x_302, 7, x_285);
lean_ctor_set(x_302, 8, x_299);
lean_ctor_set(x_302, 9, x_301);
if (lean_is_scalar(x_273)) {
 x_303 = lean_alloc_ctor(1, 1, 0);
} else {
 x_303 = x_273;
}
lean_ctor_set(x_303, 0, x_302);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_212);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_10);
lean_dec(x_9);
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_212);
return x_306;
}
}
}
block_46:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
lean_inc(x_15);
x_22 = l_List_forIn_x27_loop___at___Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0_spec__1___redArg(x_15, x_15, x_21, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_15);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_array_mk(x_10);
x_26 = l_Array_ofSubarray___redArg(x_17);
lean_dec(x_17);
x_27 = l_Array_ofSubarray___redArg(x_12);
lean_dec(x_12);
x_28 = l_Array_ofSubarray___redArg(x_14);
lean_dec(x_14);
x_29 = l_Array_ofSubarray___redArg(x_19);
lean_dec(x_19);
x_30 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_11);
lean_ctor_set(x_30, 4, x_26);
lean_ctor_set(x_30, 5, x_13);
lean_ctor_set(x_30, 6, x_27);
lean_ctor_set(x_30, 7, x_24);
lean_ctor_set(x_30, 8, x_28);
lean_ctor_set(x_30, 9, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_array_mk(x_10);
x_35 = l_Array_ofSubarray___redArg(x_17);
lean_dec(x_17);
x_36 = l_Array_ofSubarray___redArg(x_12);
lean_dec(x_12);
x_37 = l_Array_ofSubarray___redArg(x_14);
lean_dec(x_14);
x_38 = l_Array_ofSubarray___redArg(x_19);
lean_dec(x_19);
x_39 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_20);
lean_ctor_set(x_39, 3, x_11);
lean_ctor_set(x_39, 4, x_35);
lean_ctor_set(x_39, 5, x_13);
lean_ctor_set(x_39, 6, x_36);
lean_ctor_set(x_39, 7, x_32);
lean_ctor_set(x_39, 8, x_37);
lean_ctor_set(x_39, 9, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_33);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
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
lean_object* x_307; lean_object* x_308; 
lean_dec(x_8);
lean_dec(x_1);
x_307 = lean_box(0);
x_308 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___lam__0(x_307, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_308;
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
lean_inc(x_15);
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
lean_dec(x_15);
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
lean_dec(x_26);
lean_dec(x_25);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
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
lean_dec(x_51);
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
lean_dec(x_63);
x_29 = x_64;
goto block_33;
}
}
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; 
lean_dec(x_26);
lean_dec(x_25);
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
lean_dec(x_70);
lean_dec(x_69);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
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
lean_dec(x_96);
x_74 = x_97;
goto block_78;
}
}
else
{
lean_object* x_98; size_t x_99; size_t x_100; 
lean_dec(x_70);
lean_dec(x_69);
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
lean_inc(x_15);
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
lean_dec(x_15);
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
lean_dec(x_26);
lean_dec(x_25);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
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
lean_dec(x_51);
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
lean_dec(x_63);
x_29 = x_64;
goto block_33;
}
}
}
else
{
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
lean_dec(x_26);
lean_dec(x_25);
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
lean_dec(x_70);
lean_dec(x_69);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
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
lean_dec(x_96);
x_74 = x_97;
goto block_78;
}
}
else
{
lean_object* x_98; size_t x_99; size_t x_100; lean_object* x_101; 
lean_dec(x_70);
lean_dec(x_69);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal error in `split` tactic: encountered an unexpected `match` expression alternative\nthis error typically occurs when the `match` expression has been constructed using meta-programming.", 191, 191);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_44; lean_object* x_52; uint8_t x_53; 
x_52 = lean_array_get_size(x_12);
x_53 = lean_nat_dec_lt(x_52, x_8);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_nat_dec_lt(x_52, x_4);
lean_dec(x_52);
x_44 = x_54;
goto block_51;
}
else
{
lean_dec(x_52);
x_44 = x_10;
goto block_51;
}
block_43:
{
lean_object* x_20; 
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_13, x_14, x_15, x_16, x_17, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_get_size(x_12);
lean_inc(x_8);
lean_inc(x_12);
x_24 = l_Array_toSubarray___redArg(x_12, x_8, x_23);
x_25 = l_Array_ofSubarray___redArg(x_24);
lean_dec(x_24);
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Meta_mkLambdaFVars(x_25, x_21, x_9, x_10, x_9, x_10, x_27, x_14, x_15, x_16, x_17, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_nat_sub(x_8, x_4);
lean_inc(x_31);
lean_inc(x_11);
lean_inc(x_12);
x_32 = l_Array_toSubarray___redArg(x_12, x_11, x_31);
x_33 = lean_nat_dec_eq(x_4, x_11);
lean_dec(x_11);
lean_dec(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Array_toSubarray___redArg(x_12, x_31, x_8);
x_35 = l_Array_ofSubarray___redArg(x_34);
lean_dec(x_34);
x_36 = lean_box(x_9);
x_37 = lean_box(x_10);
lean_inc(x_35);
x_38 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0___boxed), 13, 6);
lean_closure_set(x_38, 0, x_29);
lean_closure_set(x_38, 1, x_35);
lean_closure_set(x_38, 2, x_32);
lean_closure_set(x_38, 3, x_36);
lean_closure_set(x_38, 4, x_37);
lean_closure_set(x_38, 5, x_26);
x_39 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_withNewAltEqs(x_3, x_6, x_35, x_38, x_14, x_15, x_16, x_17, x_30);
lean_dec(x_6);
lean_dec(x_3);
return x_39;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
lean_dec(x_31);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_40 = l_Array_ofSubarray___redArg(x_32);
lean_dec(x_32);
x_41 = lean_unbox(x_26);
x_42 = l_Lean_Meta_mkLambdaFVars(x_40, x_29, x_9, x_10, x_9, x_10, x_41, x_14, x_15, x_16, x_17, x_30);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_42;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
}
else
{
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
block_51:
{
if (x_44 == 0)
{
x_19 = x_18;
goto block_43;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1;
x_46 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_45, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_14, 1);
x_23 = lean_ctor_get(x_14, 2);
x_24 = lean_nat_dec_lt(x_16, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_array_fget(x_1, x_16);
lean_inc(x_2);
x_27 = lean_array_get(x_2, x_3, x_16);
x_28 = lean_box(x_11);
x_29 = lean_box(x_12);
lean_inc(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___boxed), 18, 11);
lean_closure_set(x_30, 0, x_4);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_6);
lean_closure_set(x_30, 3, x_7);
lean_closure_set(x_30, 4, x_8);
lean_closure_set(x_30, 5, x_9);
lean_closure_set(x_30, 6, x_10);
lean_closure_set(x_30, 7, x_27);
lean_closure_set(x_30, 8, x_28);
lean_closure_set(x_30, 9, x_29);
lean_closure_set(x_30, 10, x_13);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_31 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_26, x_30, x_11, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_push(x_15, x_32);
x_35 = lean_nat_add(x_16, x_23);
lean_dec(x_16);
x_15 = x_34;
x_16 = x_35;
x_21 = x_33;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, uint8_t x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; 
x_24 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_19, x_20, x_21, x_22, x_23);
return x_24;
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
x_17 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0(x_9, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = l_Lean_Meta_Split_simpMatch___lam__1___closed__0;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_30, 1);
x_35 = lean_ctor_get(x_30, 2);
x_36 = lean_ctor_get(x_30, 3);
x_37 = lean_ctor_get(x_30, 4);
x_38 = lean_ctor_get(x_30, 5);
x_39 = lean_ctor_get(x_30, 6);
x_40 = lean_ctor_get(x_30, 7);
x_41 = lean_ctor_get(x_30, 8);
x_42 = lean_ctor_get(x_30, 9);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_3);
lean_inc(x_3);
x_45 = l_Array_toSubarray___redArg(x_3, x_43, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_array_size(x_39);
x_49 = 0;
x_50 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(x_46, x_39, x_48, x_49, x_47, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_39);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_box(x_16);
x_55 = lean_st_ref_set(x_4, x_54, x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_58 = lean_array_get_size(x_41);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_unbox(x_19);
lean_inc(x_7);
x_62 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_41, x_5, x_40, x_2, x_3, x_1, x_6, x_7, x_8, x_4, x_61, x_16, x_43, x_60, x_57, x_43, x_10, x_11, x_12, x_13, x_56);
lean_dec(x_60);
lean_dec(x_41);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_ctor_set(x_30, 8, x_64);
lean_ctor_set(x_30, 6, x_7);
x_65 = l_Lean_Meta_MatcherApp_toExpr(x_30);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_65);
lean_ctor_set(x_62, 0, x_22);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_62, 0);
x_67 = lean_ctor_get(x_62, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_62);
lean_ctor_set(x_30, 8, x_66);
lean_ctor_set(x_30, 6, x_7);
x_68 = l_Lean_Meta_MatcherApp_toExpr(x_30);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_22);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_free_object(x_30);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_22);
lean_dec(x_7);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_62, 0);
x_72 = lean_ctor_get(x_62, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_62);
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
lean_free_object(x_30);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_50);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_50, 0);
lean_dec(x_75);
x_76 = lean_ctor_get(x_52, 0);
lean_inc(x_76);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_76);
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_50, 1);
lean_inc(x_77);
lean_dec(x_50);
x_78 = lean_ctor_get(x_52, 0);
lean_inc(x_78);
lean_dec(x_52);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_80 = lean_ctor_get(x_30, 0);
x_81 = lean_ctor_get(x_30, 1);
x_82 = lean_ctor_get(x_30, 2);
x_83 = lean_ctor_get(x_30, 3);
x_84 = lean_ctor_get(x_30, 4);
x_85 = lean_ctor_get(x_30, 5);
x_86 = lean_ctor_get(x_30, 6);
x_87 = lean_ctor_get(x_30, 7);
x_88 = lean_ctor_get(x_30, 8);
x_89 = lean_ctor_get(x_30, 9);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_30);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_array_get_size(x_3);
lean_inc(x_3);
x_92 = l_Array_toSubarray___redArg(x_3, x_90, x_91);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_array_size(x_86);
x_96 = 0;
x_97 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(x_93, x_86, x_95, x_96, x_94, x_10, x_11, x_12, x_13, x_31);
lean_dec(x_86);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = lean_box(x_16);
x_102 = lean_st_ref_set(x_4, x_101, x_100);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_105 = lean_array_get_size(x_88);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_107, 0, x_90);
lean_ctor_set(x_107, 1, x_105);
lean_ctor_set(x_107, 2, x_106);
x_108 = lean_unbox(x_19);
lean_inc(x_7);
x_109 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_88, x_5, x_87, x_2, x_3, x_1, x_6, x_7, x_8, x_4, x_108, x_16, x_90, x_107, x_104, x_90, x_10, x_11, x_12, x_13, x_103);
lean_dec(x_107);
lean_dec(x_88);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(x_113, 0, x_80);
lean_ctor_set(x_113, 1, x_81);
lean_ctor_set(x_113, 2, x_82);
lean_ctor_set(x_113, 3, x_83);
lean_ctor_set(x_113, 4, x_84);
lean_ctor_set(x_113, 5, x_85);
lean_ctor_set(x_113, 6, x_7);
lean_ctor_set(x_113, 7, x_87);
lean_ctor_set(x_113, 8, x_110);
lean_ctor_set(x_113, 9, x_89);
x_114 = l_Lean_Meta_MatcherApp_toExpr(x_113);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_114);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_22);
lean_ctor_set(x_115, 1, x_111);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_89);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_free_object(x_22);
lean_dec(x_7);
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_free_object(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_97, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_121 = x_97;
} else {
 lean_dec_ref(x_97);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
lean_dec(x_99);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_124 = lean_ctor_get(x_22, 0);
lean_inc(x_124);
lean_dec(x_22);
x_125 = lean_ctor_get(x_21, 1);
lean_inc(x_125);
lean_dec(x_21);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 4);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 5);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 6);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 7);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 8);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 9);
lean_inc(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 lean_ctor_release(x_124, 6);
 lean_ctor_release(x_124, 7);
 lean_ctor_release(x_124, 8);
 lean_ctor_release(x_124, 9);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
x_137 = lean_unsigned_to_nat(0u);
x_138 = lean_array_get_size(x_3);
lean_inc(x_3);
x_139 = l_Array_toSubarray___redArg(x_3, x_137, x_138);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_array_size(x_132);
x_143 = 0;
x_144 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4___redArg(x_140, x_132, x_142, x_143, x_141, x_10, x_11, x_12, x_13, x_125);
lean_dec(x_132);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; 
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_box(x_16);
x_149 = lean_st_ref_set(x_4, x_148, x_147);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_withEqs___redArg___closed__0;
x_152 = lean_array_get_size(x_134);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_154, 0, x_137);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_154, 2, x_153);
x_155 = lean_unbox(x_19);
lean_inc(x_7);
x_156 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_134, x_5, x_133, x_2, x_3, x_1, x_6, x_7, x_8, x_4, x_155, x_16, x_137, x_154, x_151, x_137, x_10, x_11, x_12, x_13, x_150);
lean_dec(x_154);
lean_dec(x_134);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_160 = lean_alloc_ctor(0, 10, 0);
} else {
 x_160 = x_136;
}
lean_ctor_set(x_160, 0, x_126);
lean_ctor_set(x_160, 1, x_127);
lean_ctor_set(x_160, 2, x_128);
lean_ctor_set(x_160, 3, x_129);
lean_ctor_set(x_160, 4, x_130);
lean_ctor_set(x_160, 5, x_131);
lean_ctor_set(x_160, 6, x_7);
lean_ctor_set(x_160, 7, x_133);
lean_ctor_set(x_160, 8, x_157);
lean_ctor_set(x_160, 9, x_135);
x_161 = l_Lean_Meta_MatcherApp_toExpr(x_160);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_161);
if (lean_is_scalar(x_159)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_159;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_158);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_7);
x_164 = lean_ctor_get(x_156, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_156, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_166 = x_156;
} else {
 lean_dec_ref(x_156);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 2, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_164);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_144, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_169 = x_144;
} else {
 lean_dec_ref(x_144);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_146, 0);
lean_inc(x_170);
lean_dec(x_146);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_21);
if (x_172 == 0)
{
return x_21;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_21, 0);
x_174 = lean_ctor_get(x_21, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_21);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_14 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_8, x_10, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0___boxed), 6, 0);
x_18 = lean_box(0);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__1), 14, 8);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_7);
lean_closure_set(x_19, 4, x_18);
lean_closure_set(x_19, 5, x_4);
lean_closure_set(x_19, 6, x_5);
lean_closure_set(x_19, 7, x_6);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = lean_unbox(x_20);
x_23 = l_Lean_Meta_transform___at___Lean_Meta_zetaReduce_spec__0(x_15, x_19, x_17, x_21, x_22, x_9, x_10, x_11, x_12, x_16);
return x_23;
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = lean_unbox(x_6);
lean_dec(x_6);
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__0(x_1, x_2, x_3, x_14, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___boxed(lean_object** _args) {
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
uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = lean_unbox(x_10);
lean_dec(x_10);
x_21 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_11);
lean_dec(x_11);
x_23 = lean_unbox(x_12);
lean_dec(x_12);
x_24 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22, x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_unbox(x_11);
lean_dec(x_11);
x_25 = lean_unbox(x_12);
lean_dec(x_12);
x_26 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_24, x_25, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_16);
x_19 = l_Lean_MVarId_getType(x_2, x_10, x_11, x_12, x_13, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_17);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget(x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_20, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__1;
x_30 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_29, x_10, x_11, x_12, x_13, x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_25, 1);
x_37 = lean_ctor_get(x_25, 0);
lean_dec(x_37);
x_38 = l_Array_append___redArg(x_7, x_8);
lean_dec(x_8);
x_39 = lean_box(1);
x_40 = lean_unbox(x_26);
x_41 = lean_unbox(x_26);
lean_dec(x_26);
x_42 = lean_unbox(x_39);
x_43 = l_Lean_Meta_mkForallFVars(x_38, x_23, x_1, x_40, x_41, x_42, x_10, x_11, x_12, x_13, x_36);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_44);
x_46 = l_Lean_Meta_isTypeCorrect(x_44, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_44);
lean_free_object(x_25);
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_46);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_46, 0);
lean_dec(x_56);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 0, x_44);
lean_ctor_set(x_46, 0, x_25);
return x_46;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
lean_ctor_set(x_25, 1, x_9);
lean_ctor_set(x_25, 0, x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_25);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_44);
lean_free_object(x_25);
lean_dec(x_9);
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
return x_46;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_46, 0);
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_46);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_43);
if (x_63 == 0)
{
return x_43;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_43, 0);
x_65 = lean_ctor_get(x_43, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_43);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_25, 1);
lean_inc(x_67);
lean_dec(x_25);
x_68 = l_Array_append___redArg(x_7, x_8);
lean_dec(x_8);
x_69 = lean_box(1);
x_70 = lean_unbox(x_26);
x_71 = lean_unbox(x_26);
lean_dec(x_26);
x_72 = lean_unbox(x_69);
x_73 = l_Lean_Meta_mkForallFVars(x_68, x_23, x_1, x_70, x_71, x_72, x_10, x_11, x_12, x_13, x_67);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_74);
x_76 = l_Lean_Meta_isTypeCorrect(x_74, x_10, x_11, x_12, x_13, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
lean_dec(x_9);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___closed__2;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_80;
 lean_ctor_set_tag(x_82, 1);
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_84 = x_76;
} else {
 lean_dec_ref(x_76);
 x_84 = lean_box(0);
}
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_9);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_74);
lean_dec(x_9);
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_89 = x_76;
} else {
 lean_dec_ref(x_76);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_91 = lean_ctor_get(x_73, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_73, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_93 = x_73;
} else {
 lean_dec_ref(x_73);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_95 = !lean_is_exclusive(x_22);
if (x_95 == 0)
{
return x_22;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_22, 0);
x_97 = lean_ctor_get(x_22, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_22);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
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
x_99 = !lean_is_exclusive(x_19);
if (x_99 == 0)
{
return x_19;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_19, 0);
x_101 = lean_ctor_get(x_19, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_19);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_1);
lean_inc(x_7);
lean_inc(x_4);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__2;
x_15 = l_panic___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_spec__0(x_14, x_6, x_7, x_8, x_9, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_18);
x_20 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed), 13, 6);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_18);
lean_closure_set(x_21, 5, x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_5, x_21, x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
lean_inc(x_3);
x_27 = l_Lean_MVarId_getTag(x_3, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_6);
x_30 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_25, x_28, x_6, x_7, x_8, x_9, x_29);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_83 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_84 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_83, x_8, x_33);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_free_object(x_30);
lean_free_object(x_12);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_87;
goto block_82;
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_89 = lean_ctor_get(x_84, 1);
x_90 = lean_ctor_get(x_84, 0);
lean_dec(x_90);
x_91 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_92 = l_Lean_Expr_mvarId_x21(x_32);
lean_ctor_set(x_12, 0, x_92);
lean_ctor_set_tag(x_84, 7);
lean_ctor_set(x_84, 1, x_12);
lean_ctor_set(x_84, 0, x_91);
x_93 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_93);
lean_ctor_set(x_30, 0, x_84);
x_94 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_83, x_30, x_6, x_7, x_8, x_9, x_89);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_95;
goto block_82;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
lean_dec(x_84);
x_97 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_98 = l_Lean_Expr_mvarId_x21(x_32);
lean_ctor_set(x_12, 0, x_98);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_12);
x_100 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_100);
lean_ctor_set(x_30, 0, x_99);
x_101 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_83, x_30, x_6, x_7, x_8, x_9, x_96);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_102;
goto block_82;
}
}
block_82:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
lean_inc(x_32);
x_39 = l_Lean_mkAppN(x_32, x_4);
x_40 = l_Lean_mkAppN(x_39, x_26);
lean_dec(x_26);
x_41 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_40, x_35, x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
x_44 = lean_array_get_size(x_4);
lean_dec(x_4);
x_45 = lean_box(0);
x_46 = lean_box(1);
x_47 = lean_unbox(x_46);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_44);
x_48 = l_Lean_Meta_introNCore(x_43, x_44, x_45, x_1, x_47, x_34, x_35, x_36, x_37, x_42);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
x_54 = lean_unbox(x_46);
x_55 = l_Lean_Meta_introNCore(x_53, x_44, x_45, x_1, x_54, x_34, x_35, x_36, x_37, x_50);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_49, 1, x_57);
lean_ctor_set(x_55, 0, x_49);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set(x_49, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_49);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
else
{
uint8_t x_61; 
lean_free_object(x_49);
lean_dec(x_52);
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_55, 0);
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_55);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_49, 0);
x_66 = lean_ctor_get(x_49, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_49);
x_67 = lean_unbox(x_46);
x_68 = l_Lean_Meta_introNCore(x_66, x_44, x_45, x_1, x_67, x_34, x_35, x_36, x_37, x_50);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_69);
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
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
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_44);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_78 = !lean_is_exclusive(x_48);
if (x_78 == 0)
{
return x_48;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_48, 0);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_48);
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
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_103 = lean_ctor_get(x_30, 0);
x_104 = lean_ctor_get(x_30, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_30);
x_141 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_142 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_141, x_8, x_104);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
lean_free_object(x_12);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_105 = x_6;
x_106 = x_7;
x_107 = x_8;
x_108 = x_9;
x_109 = x_145;
goto block_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_146 = lean_ctor_get(x_142, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
x_148 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_149 = l_Lean_Expr_mvarId_x21(x_103);
lean_ctor_set(x_12, 0, x_149);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(7, 2, 0);
} else {
 x_150 = x_147;
 lean_ctor_set_tag(x_150, 7);
}
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_12);
x_151 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_141, x_152, x_6, x_7, x_8, x_9, x_146);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_105 = x_6;
x_106 = x_7;
x_107 = x_8;
x_108 = x_9;
x_109 = x_154;
goto block_140;
}
block_140:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
lean_inc(x_103);
x_110 = l_Lean_mkAppN(x_103, x_4);
x_111 = l_Lean_mkAppN(x_110, x_26);
lean_dec(x_26);
x_112 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_111, x_106, x_109);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Expr_mvarId_x21(x_103);
lean_dec(x_103);
x_115 = lean_array_get_size(x_4);
lean_dec(x_4);
x_116 = lean_box(0);
x_117 = lean_box(1);
x_118 = lean_unbox(x_117);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_115);
x_119 = l_Lean_Meta_introNCore(x_114, x_115, x_116, x_1, x_118, x_105, x_106, x_107, x_108, x_113);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_124 = x_120;
} else {
 lean_dec_ref(x_120);
 x_124 = lean_box(0);
}
x_125 = lean_unbox(x_117);
x_126 = l_Lean_Meta_introNCore(x_123, x_115, x_116, x_1, x_125, x_105, x_106, x_107, x_108, x_121);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_127);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_124);
lean_dec(x_122);
x_132 = lean_ctor_get(x_126, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_126, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_134 = x_126;
} else {
 lean_dec_ref(x_126);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_115);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_136 = lean_ctor_get(x_119, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_119, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_138 = x_119;
} else {
 lean_dec_ref(x_119);
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
}
}
else
{
uint8_t x_155; 
lean_dec(x_26);
lean_dec(x_25);
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_155 = !lean_is_exclusive(x_27);
if (x_155 == 0)
{
return x_27;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_27, 0);
x_157 = lean_ctor_get(x_27, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_27);
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
lean_free_object(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_159 = !lean_is_exclusive(x_22);
if (x_159 == 0)
{
return x_22;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_22, 0);
x_161 = lean_ctor_get(x_22, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_22);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_12, 0);
lean_inc(x_163);
lean_dec(x_12);
x_164 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_163);
x_165 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_166 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed), 13, 6);
lean_closure_set(x_166, 0, x_165);
lean_closure_set(x_166, 1, x_3);
lean_closure_set(x_166, 2, x_2);
lean_closure_set(x_166, 3, x_4);
lean_closure_set(x_166, 4, x_163);
lean_closure_set(x_166, 5, x_164);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_167 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_5, x_166, x_1, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
lean_dec(x_168);
lean_inc(x_3);
x_172 = l_Lean_MVarId_getTag(x_3, x_6, x_7, x_8, x_9, x_169);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_6);
x_175 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_170, x_173, x_6, x_7, x_8, x_9, x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_215 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_216 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_215, x_8, x_177);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
lean_dec(x_178);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_179 = x_6;
x_180 = x_7;
x_181 = x_8;
x_182 = x_9;
x_183 = x_219;
goto block_214;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_220 = lean_ctor_get(x_216, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_221 = x_216;
} else {
 lean_dec_ref(x_216);
 x_221 = lean_box(0);
}
x_222 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__4;
x_223 = l_Lean_Expr_mvarId_x21(x_176);
x_224 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_224, 0, x_223);
if (lean_is_scalar(x_221)) {
 x_225 = lean_alloc_ctor(7, 2, 0);
} else {
 x_225 = x_221;
 lean_ctor_set_tag(x_225, 7);
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_224);
x_226 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
if (lean_is_scalar(x_178)) {
 x_227 = lean_alloc_ctor(7, 2, 0);
} else {
 x_227 = x_178;
 lean_ctor_set_tag(x_227, 7);
}
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_215, x_227, x_6, x_7, x_8, x_9, x_220);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec(x_228);
x_179 = x_6;
x_180 = x_7;
x_181 = x_8;
x_182 = x_9;
x_183 = x_229;
goto block_214;
}
block_214:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
lean_inc(x_176);
x_184 = l_Lean_mkAppN(x_176, x_4);
x_185 = l_Lean_mkAppN(x_184, x_171);
lean_dec(x_171);
x_186 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_3, x_185, x_180, x_183);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = l_Lean_Expr_mvarId_x21(x_176);
lean_dec(x_176);
x_189 = lean_array_get_size(x_4);
lean_dec(x_4);
x_190 = lean_box(0);
x_191 = lean_box(1);
x_192 = lean_unbox(x_191);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_189);
x_193 = l_Lean_Meta_introNCore(x_188, x_189, x_190, x_1, x_192, x_179, x_180, x_181, x_182, x_187);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_194, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_194, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_198 = x_194;
} else {
 lean_dec_ref(x_194);
 x_198 = lean_box(0);
}
x_199 = lean_unbox(x_191);
x_200 = l_Lean_Meta_introNCore(x_197, x_189, x_190, x_1, x_199, x_179, x_180, x_181, x_182, x_195);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_198;
}
lean_ctor_set(x_204, 0, x_196);
lean_ctor_set(x_204, 1, x_201);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_198);
lean_dec(x_196);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_189);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
x_210 = lean_ctor_get(x_193, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_193, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_212 = x_193;
} else {
 lean_dec_ref(x_193);
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
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_230 = lean_ctor_get(x_172, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_172, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_232 = x_172;
} else {
 lean_dec_ref(x_172);
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
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_234 = lean_ctor_get(x_167, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_167, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_236 = x_167;
} else {
 lean_dec_ref(x_167);
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
}
else
{
size_t x_238; size_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_238 = lean_array_size(x_4);
x_239 = 0;
x_240 = l_Array_mapMUnsafe_map___at___Lean_Meta_introNCore_spec__4(x_238, x_239, x_4);
x_241 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___closed__5;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_3);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_10);
return x_244;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_4);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_16);
x_18 = lean_box(1);
x_19 = lean_unbox(x_18);
x_10 = x_19;
goto block_14;
}
else
{
if (x_17 == 0)
{
lean_dec(x_16);
x_10 = x_17;
goto block_14;
}
else
{
size_t x_20; size_t x_21; uint8_t x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_anyMUnsafe_any___at___Lean_PrettyPrinter_Delaborator_delabDelayedAssignedMVar_spec__1(x_4, x_20, x_21);
if (x_22 == 0)
{
x_10 = x_17;
goto block_14;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_10 = x_24;
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__0(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_27);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_heqToEq(x_25, x_29, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = lean_unbox(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
lean_inc(x_33);
lean_inc(x_34);
x_38 = l_Lean_Meta_substCore_x3f(x_34, x_33, x_36, x_24, x_21, x_37, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_35);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
lean_inc(x_34);
x_42 = l_Lean_Meta_substCore_x3f(x_34, x_33, x_21, x_24, x_21, x_41, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_ctor_set(x_4, 1, x_34);
x_10 = x_4;
x_11 = x_44;
goto block_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_24);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_16 = x_47;
x_17 = x_48;
x_18 = x_46;
goto block_20;
}
}
else
{
uint8_t x_49; 
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_4);
lean_dec(x_24);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
lean_dec(x_39);
x_54 = lean_ctor_get(x_38, 1);
lean_inc(x_54);
lean_dec(x_38);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_16 = x_55;
x_17 = x_56;
x_18 = x_54;
goto block_20;
}
}
else
{
uint8_t x_57; 
lean_dec(x_34);
lean_dec(x_33);
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_free_object(x_4);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_30);
if (x_61 == 0)
{
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_30, 0);
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_30);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_dec(x_28);
x_10 = x_4;
x_11 = x_9;
goto block_15;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_ctor_get(x_4, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_4);
x_67 = lean_array_uget(x_1, x_3);
x_68 = l_Lean_Expr_fvar___override(x_67);
lean_inc(x_65);
x_69 = l_Lean_Meta_FVarSubst_apply(x_65, x_68);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_71 = l_Lean_Meta_heqToEq(x_66, x_70, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_box(0);
x_77 = lean_unbox(x_76);
x_78 = lean_unbox(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_65);
lean_inc(x_74);
lean_inc(x_75);
x_79 = l_Lean_Meta_substCore_x3f(x_75, x_74, x_77, x_65, x_21, x_78, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_unbox(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_65);
lean_inc(x_75);
x_83 = l_Lean_Meta_substCore_x3f(x_75, x_74, x_21, x_65, x_21, x_82, x_5, x_6, x_7, x_8, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_65);
lean_ctor_set(x_86, 1, x_75);
x_10 = x_86;
x_11 = x_85;
goto block_15;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
lean_dec(x_65);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_16 = x_89;
x_17 = x_90;
x_18 = x_88;
goto block_20;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_75);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_93 = x_83;
} else {
 lean_dec_ref(x_83);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_65);
x_95 = lean_ctor_get(x_80, 0);
lean_inc(x_95);
lean_dec(x_80);
x_96 = lean_ctor_get(x_79, 1);
lean_inc(x_96);
lean_dec(x_79);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
lean_dec(x_95);
x_16 = x_97;
x_17 = x_98;
x_18 = x_96;
goto block_20;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_99 = lean_ctor_get(x_79, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_101 = x_79;
} else {
 lean_dec_ref(x_79);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_103 = lean_ctor_get(x_71, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_71, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_105 = x_71;
} else {
 lean_dec_ref(x_71);
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
else
{
lean_object* x_107; 
lean_dec(x_69);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_65);
lean_ctor_set(x_107, 1, x_66);
x_10 = x_107;
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
lean_dec(x_1);
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
lean_dec(x_1);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
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
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_3);
x_47 = l_Lean_Meta_introNCore(x_17, x_44, x_3, x_4, x_46, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
lean_inc(x_8);
x_128 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_13, x_49);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_52 = x_11;
x_53 = x_12;
x_54 = x_13;
x_55 = x_14;
x_56 = x_131;
goto block_127;
}
else
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_128);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_133 = lean_ctor_get(x_128, 1);
x_134 = lean_ctor_get(x_128, 0);
lean_dec(x_134);
x_135 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3;
lean_inc(x_50);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_50);
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_136);
lean_ctor_set(x_128, 0, x_135);
x_137 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_128);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_8);
x_139 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_138, x_11, x_12, x_13, x_14, x_133);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_52 = x_11;
x_53 = x_12;
x_54 = x_13;
x_55 = x_14;
x_56 = x_140;
goto block_127;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_128, 1);
lean_inc(x_141);
lean_dec(x_128);
x_142 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__3;
lean_inc(x_50);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_50);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_8);
x_147 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_146, x_11, x_12, x_13, x_14, x_141);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_52 = x_11;
x_53 = x_12;
x_54 = x_13;
x_55 = x_14;
x_56 = x_148;
goto block_127;
}
}
block_127:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l_Lean_Meta_Match_MatcherInfo_getNumDiscrEqs(x_5);
x_58 = lean_nat_add(x_6, x_57);
lean_dec(x_57);
x_59 = lean_box(0);
x_60 = lean_box(0);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
x_61 = l_Lean_Meta_Cases_unifyEqs_x3f(x_58, x_50, x_59, x_60, x_52, x_53, x_54, x_55, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_19);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_20, x_64);
lean_dec(x_20);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_21);
x_9 = x_66;
x_10 = x_18;
x_15 = x_63;
goto _start;
}
else
{
uint8_t x_68; 
lean_dec(x_51);
x_68 = !lean_is_exclusive(x_62);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_8);
x_74 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_54, x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
lean_free_object(x_69);
lean_free_object(x_62);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_23 = x_73;
x_24 = x_72;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_77;
goto block_42;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_74, 1);
x_80 = lean_ctor_get(x_74, 0);
lean_dec(x_80);
x_81 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_72);
lean_ctor_set(x_62, 0, x_72);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_62);
lean_ctor_set(x_74, 0, x_81);
x_82 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_82);
lean_ctor_set(x_69, 0, x_74);
lean_inc(x_8);
x_83 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_69, x_52, x_53, x_54, x_55, x_79);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_23 = x_73;
x_24 = x_72;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_84;
goto block_42;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_74, 1);
lean_inc(x_85);
lean_dec(x_74);
x_86 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_72);
lean_ctor_set(x_62, 0, x_72);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_62);
x_88 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_88);
lean_ctor_set(x_69, 0, x_87);
lean_inc(x_8);
x_89 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_69, x_52, x_53, x_54, x_55, x_85);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_23 = x_73;
x_24 = x_72;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_90;
goto block_42;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_69, 0);
x_92 = lean_ctor_get(x_69, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_69);
lean_inc(x_8);
x_93 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_54, x_70);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_free_object(x_62);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_23 = x_92;
x_24 = x_91;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_96;
goto block_42;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_98 = x_93;
} else {
 lean_dec_ref(x_93);
 x_98 = lean_box(0);
}
x_99 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_91);
lean_ctor_set(x_62, 0, x_91);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(7, 2, 0);
} else {
 x_100 = x_98;
 lean_ctor_set_tag(x_100, 7);
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_62);
x_101 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
lean_inc(x_8);
x_103 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_102, x_52, x_53, x_54, x_55, x_97);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_23 = x_92;
x_24 = x_91;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_104;
goto block_42;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_105 = lean_ctor_get(x_62, 0);
lean_inc(x_105);
lean_dec(x_62);
x_106 = lean_ctor_get(x_61, 1);
lean_inc(x_106);
lean_dec(x_61);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
lean_inc(x_8);
x_110 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_8, x_54, x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_109);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_23 = x_108;
x_24 = x_107;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_113;
goto block_42;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_115 = x_110;
} else {
 lean_dec_ref(x_110);
 x_115 = lean_box(0);
}
x_116 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0___closed__1;
lean_inc(x_107);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_107);
if (lean_is_scalar(x_115)) {
 x_118 = lean_alloc_ctor(7, 2, 0);
} else {
 x_118 = x_115;
 lean_ctor_set_tag(x_118, 7);
}
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(7, 2, 0);
} else {
 x_120 = x_109;
 lean_ctor_set_tag(x_120, 7);
}
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
lean_inc(x_8);
x_121 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_8, x_120, x_52, x_53, x_54, x_55, x_114);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_23 = x_108;
x_24 = x_107;
x_25 = x_52;
x_26 = x_53;
x_27 = x_54;
x_28 = x_55;
x_29 = x_122;
goto block_42;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_123 = !lean_is_exclusive(x_61);
if (x_123 == 0)
{
return x_61;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_61, 0);
x_125 = lean_ctor_get(x_61, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_61);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_47);
if (x_149 == 0)
{
return x_47;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_47, 0);
x_151 = lean_ctor_get(x_47, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_47);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
block_42:
{
lean_object* x_30; 
lean_inc(x_7);
x_30 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_substDiscrEqs(x_24, x_23, x_7, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
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
lean_inc(x_1);
x_20 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_3, x_4, x_3, x_4, x_5, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_50; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_app___override(x_6, x_21);
x_24 = l_Lean_mkAppN(x_23, x_1);
lean_dec(x_1);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_24);
x_50 = l_Lean_Meta_check(x_24, x_15, x_16, x_17, x_18, x_22);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
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
lean_dec(x_52);
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
lean_dec(x_52);
x_57 = l_Lean_Meta_Split_applyMatchSplitter___lam__0___closed__2;
lean_inc(x_7);
x_58 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_7, x_57, x_15, x_16, x_17, x_18, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
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
lean_dec(x_24);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
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
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_31 = l_Lean_MVarId_applyN(x_9, x_24, x_30, x_4, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
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
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_14);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_dec(x_2);
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
lean_dec(x_8);
x_18 = l_Lean_Meta_Split_applyMatchSplitter___lam__1___closed__1;
x_19 = lean_array_size(x_2);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_19, x_20, x_2);
x_22 = lean_array_to_list(x_21);
x_23 = lean_box(0);
x_24 = l_List_mapTR_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___Lean_Meta_mkAppM_spec__0_spec__0(x_22, x_23);
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
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_32 = lean_get_match_equations_for(x_2, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_inc(x_3);
x_36 = lean_array_to_list(x_3);
lean_inc(x_35);
x_37 = l_Lean_Expr_const___override(x_35, x_36);
x_38 = l_Lean_mkAppN(x_37, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = lean_infer_type(x_38, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_42 = l_Lean_Meta_whnfForall(x_40, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_119; lean_object* x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_284; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
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
x_50 = lean_box(0);
x_182 = l_Lean_Expr_bindingDomain_x21(x_43);
lean_dec(x_43);
x_284 = lean_unbox(x_47);
lean_dec(x_47);
if (x_284 == 0)
{
x_230 = x_6;
x_231 = x_7;
x_232 = x_8;
x_233 = x_9;
x_234 = x_48;
goto block_283;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_285 = l_Lean_Meta_Split_applyMatchSplitter___closed__15;
lean_inc(x_1);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_1);
x_287 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
x_290 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_289, x_6, x_7, x_8, x_9, x_48);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_230 = x_6;
x_231 = x_7;
x_232 = x_8;
x_233 = x_9;
x_234 = x_291;
goto block_283;
}
block_73:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_array_to_list(x_59);
x_66 = l_Lean_Expr_const___override(x_35, x_65);
x_67 = l_Lean_mkAppN(x_66, x_4);
x_68 = lean_box(1);
x_69 = lean_box(1);
x_70 = lean_box(x_52);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__0___boxed), 19, 14);
lean_closure_set(x_71, 0, x_53);
lean_closure_set(x_71, 1, x_54);
lean_closure_set(x_71, 2, x_70);
lean_closure_set(x_71, 3, x_68);
lean_closure_set(x_71, 4, x_69);
lean_closure_set(x_71, 5, x_67);
lean_closure_set(x_71, 6, x_45);
lean_closure_set(x_71, 7, x_33);
lean_closure_set(x_71, 8, x_57);
lean_closure_set(x_71, 9, x_50);
lean_closure_set(x_71, 10, x_51);
lean_closure_set(x_71, 11, x_30);
lean_closure_set(x_71, 12, x_55);
lean_closure_set(x_71, 13, x_56);
x_72 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_58, x_71, x_60, x_61, x_62, x_63, x_64);
return x_72;
}
block_118:
{
lean_object* x_87; 
lean_inc(x_80);
x_87 = l_Lean_MVarId_getType(x_80, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_88);
x_90 = lean_alloc_closure((void*)(l_Lean_Meta_getLevel), 6, 1);
lean_closure_set(x_90, 0, x_88);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_80);
x_91 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_80, x_90, x_82, x_83, x_84, x_85, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; size_t x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_30, 3);
lean_inc(x_94);
x_95 = lean_array_size(x_79);
x_96 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_95, x_81, x_79);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_97; 
x_97 = l_Lean_Level_isZero(x_92);
lean_dec(x_92);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_96);
lean_dec(x_88);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_3);
x_98 = l_Lean_Meta_Split_applyMatchSplitter___closed__5;
x_99 = l_Lean_MessageData_ofName(x_35);
if (lean_is_scalar(x_49)) {
 x_100 = lean_alloc_ctor(7, 2, 0);
} else {
 x_100 = x_49;
 lean_ctor_set_tag(x_100, 7);
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Meta_Split_applyMatchSplitter___closed__7;
if (lean_is_scalar(x_29)) {
 x_102 = lean_alloc_ctor(7, 2, 0);
} else {
 x_102 = x_29;
 lean_ctor_set_tag(x_102, 7);
}
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_102, x_82, x_83, x_84, x_85, x_93);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
lean_dec(x_49);
lean_dec(x_29);
x_51 = x_75;
x_52 = x_74;
x_53 = x_96;
x_54 = x_88;
x_55 = x_76;
x_56 = x_77;
x_57 = x_78;
x_58 = x_80;
x_59 = x_3;
x_60 = x_82;
x_61 = x_83;
x_62 = x_84;
x_63 = x_85;
x_64 = x_93;
goto block_73;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_49);
lean_dec(x_29);
x_108 = lean_ctor_get(x_94, 0);
lean_inc(x_108);
lean_dec(x_94);
x_109 = lean_array_set(x_3, x_108, x_92);
lean_dec(x_108);
x_51 = x_75;
x_52 = x_74;
x_53 = x_96;
x_54 = x_88;
x_55 = x_76;
x_56 = x_77;
x_57 = x_78;
x_58 = x_80;
x_59 = x_109;
x_60 = x_82;
x_61 = x_83;
x_62 = x_84;
x_63 = x_85;
x_64 = x_93;
goto block_73;
}
}
else
{
uint8_t x_110; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_91);
if (x_110 == 0)
{
return x_91;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_91, 0);
x_112 = lean_ctor_get(x_91, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_91);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_87);
if (x_114 == 0)
{
return x_87;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_87, 0);
x_116 = lean_ctor_get(x_87, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_87);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_181:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; 
x_127 = lean_array_get_size(x_5);
lean_dec(x_5);
x_128 = lean_box(0);
x_129 = lean_box(0);
x_130 = lean_unbox(x_129);
x_131 = lean_unbox(x_129);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_127);
x_132 = l_Lean_Meta_introNCore(x_120, x_127, x_128, x_130, x_131, x_122, x_123, x_124, x_125, x_126);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_133, 0);
x_137 = lean_ctor_get(x_133, 1);
x_138 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_124, x_134);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; uint8_t x_142; 
lean_free_object(x_133);
lean_dec(x_31);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_unbox(x_129);
lean_inc(x_137);
x_74 = x_142;
x_75 = x_128;
x_76 = x_127;
x_77 = x_119;
x_78 = x_137;
x_79 = x_136;
x_80 = x_137;
x_81 = x_121;
x_82 = x_122;
x_83 = x_123;
x_84 = x_124;
x_85 = x_125;
x_86 = x_141;
goto block_118;
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_138);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_144 = lean_ctor_get(x_138, 1);
x_145 = lean_ctor_get(x_138, 0);
lean_dec(x_145);
x_146 = l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_inc(x_137);
if (lean_is_scalar(x_31)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_31;
}
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set_tag(x_138, 7);
lean_ctor_set(x_138, 1, x_147);
lean_ctor_set(x_138, 0, x_146);
x_148 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_133, 7);
lean_ctor_set(x_133, 1, x_148);
lean_ctor_set(x_133, 0, x_138);
x_149 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_133, x_122, x_123, x_124, x_125, x_144);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_unbox(x_129);
lean_inc(x_137);
x_74 = x_151;
x_75 = x_128;
x_76 = x_127;
x_77 = x_119;
x_78 = x_137;
x_79 = x_136;
x_80 = x_137;
x_81 = x_121;
x_82 = x_122;
x_83 = x_123;
x_84 = x_124;
x_85 = x_125;
x_86 = x_150;
goto block_118;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
lean_dec(x_138);
x_153 = l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_inc(x_137);
if (lean_is_scalar(x_31)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_31;
}
lean_ctor_set(x_154, 0, x_137);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_133, 7);
lean_ctor_set(x_133, 1, x_156);
lean_ctor_set(x_133, 0, x_155);
x_157 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_133, x_122, x_123, x_124, x_125, x_152);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_unbox(x_129);
lean_inc(x_137);
x_74 = x_159;
x_75 = x_128;
x_76 = x_127;
x_77 = x_119;
x_78 = x_137;
x_79 = x_136;
x_80 = x_137;
x_81 = x_121;
x_82 = x_122;
x_83 = x_123;
x_84 = x_124;
x_85 = x_125;
x_86 = x_158;
goto block_118;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_160 = lean_ctor_get(x_133, 0);
x_161 = lean_ctor_get(x_133, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_133);
x_162 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_124, x_134);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_31);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
x_166 = lean_unbox(x_129);
lean_inc(x_161);
x_74 = x_166;
x_75 = x_128;
x_76 = x_127;
x_77 = x_119;
x_78 = x_161;
x_79 = x_160;
x_80 = x_161;
x_81 = x_121;
x_82 = x_122;
x_83 = x_123;
x_84 = x_124;
x_85 = x_125;
x_86 = x_165;
goto block_118;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_167 = lean_ctor_get(x_162, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_168 = x_162;
} else {
 lean_dec_ref(x_162);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Meta_Split_applyMatchSplitter___closed__9;
lean_inc(x_161);
if (lean_is_scalar(x_31)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_31;
}
lean_ctor_set(x_170, 0, x_161);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_168;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_173, x_122, x_123, x_124, x_125, x_167);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_unbox(x_129);
lean_inc(x_161);
x_74 = x_176;
x_75 = x_128;
x_76 = x_127;
x_77 = x_119;
x_78 = x_161;
x_79 = x_160;
x_80 = x_161;
x_81 = x_121;
x_82 = x_122;
x_83 = x_123;
x_84 = x_124;
x_85 = x_125;
x_86 = x_175;
goto block_118;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_3);
x_177 = !lean_is_exclusive(x_132);
if (x_177 == 0)
{
return x_132;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_132, 0);
x_179 = lean_ctor_get(x_132, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_132);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
block_229:
{
size_t x_192; size_t x_193; lean_object* x_194; lean_object* x_195; 
x_192 = lean_array_size(x_186);
x_193 = 0;
x_194 = l_Array_mapMUnsafe_map___at___Lean_LocalContext_getFVars_spec__0(x_192, x_193, x_186);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
x_195 = l_Lean_Meta_generalizeTargetsEq(x_184, x_182, x_194, x_187, x_188, x_189, x_190, x_191);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_196);
x_198 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_196, x_185, x_187, x_188, x_189, x_190, x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_189, x_199);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_unbox(x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_119 = x_183;
x_120 = x_196;
x_121 = x_193;
x_122 = x_187;
x_123 = x_188;
x_124 = x_189;
x_125 = x_190;
x_126 = x_203;
goto block_181;
}
else
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_200);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_205 = lean_ctor_get(x_200, 1);
x_206 = lean_ctor_get(x_200, 0);
lean_dec(x_206);
x_207 = l_Lean_Meta_Split_applyMatchSplitter___closed__11;
lean_inc(x_196);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_196);
lean_ctor_set_tag(x_200, 7);
lean_ctor_set(x_200, 1, x_208);
lean_ctor_set(x_200, 0, x_207);
x_209 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_210, x_187, x_188, x_189, x_190, x_205);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_119 = x_183;
x_120 = x_196;
x_121 = x_193;
x_122 = x_187;
x_123 = x_188;
x_124 = x_189;
x_125 = x_190;
x_126 = x_212;
goto block_181;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_200, 1);
lean_inc(x_213);
lean_dec(x_200);
x_214 = l_Lean_Meta_Split_applyMatchSplitter___closed__11;
lean_inc(x_196);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_196);
x_216 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_218, x_187, x_188, x_189, x_190, x_213);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_119 = x_183;
x_120 = x_196;
x_121 = x_193;
x_122 = x_187;
x_123 = x_188;
x_124 = x_189;
x_125 = x_190;
x_126 = x_220;
goto block_181;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_196);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_183);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_3);
x_221 = !lean_is_exclusive(x_198);
if (x_221 == 0)
{
return x_198;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_198, 0);
x_223 = lean_ctor_get(x_198, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_198);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_3);
x_225 = !lean_is_exclusive(x_195);
if (x_225 == 0)
{
return x_195;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_195, 0);
x_227 = lean_ctor_get(x_195, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_195);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
block_283:
{
lean_object* x_235; 
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_5);
lean_inc(x_182);
x_235 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs(x_1, x_2, x_182, x_5, x_230, x_231, x_232, x_233, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
lean_dec(x_236);
x_240 = !lean_is_exclusive(x_237);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_241 = lean_ctor_get(x_237, 0);
x_242 = lean_ctor_get(x_237, 1);
x_243 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_232, x_238);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_245 = lean_ctor_get(x_243, 0);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_241);
x_247 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed), 7, 2);
lean_closure_set(x_247, 0, x_45);
lean_closure_set(x_247, 1, x_241);
x_248 = lean_unbox(x_245);
lean_dec(x_245);
if (x_248 == 0)
{
lean_free_object(x_243);
lean_free_object(x_237);
x_183 = x_241;
x_184 = x_242;
x_185 = x_247;
x_186 = x_239;
x_187 = x_230;
x_188 = x_231;
x_189 = x_232;
x_190 = x_233;
x_191 = x_246;
goto block_229;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_249 = l_Lean_Meta_Split_applyMatchSplitter___closed__13;
lean_inc(x_242);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set_tag(x_243, 7);
lean_ctor_set(x_243, 1, x_250);
lean_ctor_set(x_243, 0, x_249);
x_251 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_237, 7);
lean_ctor_set(x_237, 1, x_251);
lean_ctor_set(x_237, 0, x_243);
x_252 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_237, x_230, x_231, x_232, x_233, x_246);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_183 = x_241;
x_184 = x_242;
x_185 = x_247;
x_186 = x_239;
x_187 = x_230;
x_188 = x_231;
x_189 = x_232;
x_190 = x_233;
x_191 = x_253;
goto block_229;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = lean_ctor_get(x_243, 0);
x_255 = lean_ctor_get(x_243, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_243);
lean_inc(x_241);
x_256 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed), 7, 2);
lean_closure_set(x_256, 0, x_45);
lean_closure_set(x_256, 1, x_241);
x_257 = lean_unbox(x_254);
lean_dec(x_254);
if (x_257 == 0)
{
lean_free_object(x_237);
x_183 = x_241;
x_184 = x_242;
x_185 = x_256;
x_186 = x_239;
x_187 = x_230;
x_188 = x_231;
x_189 = x_232;
x_190 = x_233;
x_191 = x_255;
goto block_229;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_258 = l_Lean_Meta_Split_applyMatchSplitter___closed__13;
lean_inc(x_242);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_242);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
lean_ctor_set_tag(x_237, 7);
lean_ctor_set(x_237, 1, x_261);
lean_ctor_set(x_237, 0, x_260);
x_262 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_237, x_230, x_231, x_232, x_233, x_255);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_183 = x_241;
x_184 = x_242;
x_185 = x_256;
x_186 = x_239;
x_187 = x_230;
x_188 = x_231;
x_189 = x_232;
x_190 = x_233;
x_191 = x_263;
goto block_229;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_264 = lean_ctor_get(x_237, 0);
x_265 = lean_ctor_get(x_237, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_237);
x_266 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_45, x_232, x_238);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
lean_inc(x_264);
x_270 = lean_alloc_closure((void*)(l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed), 7, 2);
lean_closure_set(x_270, 0, x_45);
lean_closure_set(x_270, 1, x_264);
x_271 = lean_unbox(x_267);
lean_dec(x_267);
if (x_271 == 0)
{
lean_dec(x_269);
x_183 = x_264;
x_184 = x_265;
x_185 = x_270;
x_186 = x_239;
x_187 = x_230;
x_188 = x_231;
x_189 = x_232;
x_190 = x_233;
x_191 = x_268;
goto block_229;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = l_Lean_Meta_Split_applyMatchSplitter___closed__13;
lean_inc(x_265);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_265);
if (lean_is_scalar(x_269)) {
 x_274 = lean_alloc_ctor(7, 2, 0);
} else {
 x_274 = x_269;
 lean_ctor_set_tag(x_274, 7);
}
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_276 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_45, x_276, x_230, x_231, x_232, x_233, x_268);
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_183 = x_264;
x_184 = x_265;
x_185 = x_270;
x_186 = x_239;
x_187 = x_230;
x_188 = x_231;
x_189 = x_232;
x_190 = x_233;
x_191 = x_278;
goto block_229;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_182);
lean_dec(x_49);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_3);
x_279 = !lean_is_exclusive(x_235);
if (x_279 == 0)
{
return x_235;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_235, 0);
x_281 = lean_ctor_get(x_235, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_235);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_292 = !lean_is_exclusive(x_42);
if (x_292 == 0)
{
return x_42;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_42, 0);
x_294 = lean_ctor_get(x_42, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_42);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set(x_295, 1, x_294);
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_39);
if (x_296 == 0)
{
return x_39;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_39, 0);
x_298 = lean_ctor_get(x_39, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_39);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_32);
if (x_300 == 0)
{
return x_32;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_32, 0);
x_302 = lean_ctor_get(x_32, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_32);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
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
lean_dec(x_4);
x_17 = l_List_foldlM___at___Lean_Meta_Split_applyMatchSplitter_spec__0(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_dec(x_3);
x_21 = lean_unbox(x_4);
lean_dec(x_4);
x_22 = lean_unbox(x_5);
lean_dec(x_5);
x_23 = l_Lean_Meta_Split_applyMatchSplitter___lam__0(x_1, x_2, x_20, x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Split_applyMatchSplitter___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_applyMatchSplitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Split_applyMatchSplitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_throwDiscrGenError___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Split_throwDiscrGenError(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_20 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_14, x_3, x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_36 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_30, x_3, x_35, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_54 = l___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_simpMatchTargetCore(x_47, x_3, x_53, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
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
lean_dec(x_10);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 6);
lean_inc(x_24);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_21);
x_25 = lean_get_match_equations_for(x_21, x_5, x_6, x_7, x_8, x_20);
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
lean_inc(x_21);
x_28 = l_Lean_Meta_Split_applyMatchSplitter(x_3, x_21, x_22, x_23, x_24, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_28;
}
}
else
{
uint8_t x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(0);
x_9 = lean_box(0);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Split_splitMatch___lam__0___boxed), 9, 4);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_8);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___at___Lean_Meta_Split_splitMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Split_splitMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_176; 
if (x_2 == 0)
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_box(1);
x_244 = lean_unbox(x_243);
x_176 = x_244;
goto block_242;
}
else
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_box(2);
x_246 = lean_unbox(x_245);
x_176 = x_246;
goto block_242;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_71:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Meta_splitIfTarget_x3f(x_1, x_15, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 1);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_27);
lean_ctor_set(x_17, 0, x_26);
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 1, x_37);
lean_ctor_set(x_17, 0, x_26);
return x_16;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
lean_dec(x_26);
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_40 = x_27;
} else {
 lean_dec_ref(x_27);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_40;
 lean_ctor_set_tag(x_42, 1);
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_17, 0, x_43);
return x_16;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_26, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_46 = x_26;
} else {
 lean_dec_ref(x_26);
 x_46 = lean_box(0);
}
x_47 = lean_ctor_get(x_27, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_48 = x_27;
} else {
 lean_dec_ref(x_27);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_48;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_46;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_17, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_17);
lean_ctor_set(x_52, 1, x_44);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_53 = lean_ctor_get(x_17, 0);
lean_inc(x_53);
lean_dec(x_17);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_57 = x_16;
} else {
 lean_dec_ref(x_16);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_61 = x_55;
} else {
 lean_dec_ref(x_55);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_61;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_59;
 lean_ctor_set_tag(x_64, 1);
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
}
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
block_129:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; size_t x_88; size_t x_89; size_t x_90; size_t x_91; size_t x_92; lean_object* x_93; uint8_t x_94; 
x_78 = lean_ctor_get(x_4, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
x_80 = lean_array_get_size(x_79);
x_81 = l_Lean_Expr_hash(x_72);
x_82 = 32;
x_83 = lean_uint64_shift_right(x_81, x_82);
x_84 = lean_uint64_xor(x_81, x_83);
x_85 = 16;
x_86 = lean_uint64_shift_right(x_84, x_85);
x_87 = lean_uint64_xor(x_84, x_86);
x_88 = lean_uint64_to_usize(x_87);
x_89 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_90 = 1;
x_91 = lean_usize_sub(x_89, x_90);
x_92 = lean_usize_land(x_88, x_91);
x_93 = lean_array_uget(x_79, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectLevelParams_visitExpr_spec__0___redArg(x_72, x_93);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_4);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_96 = lean_ctor_get(x_4, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_4, 0);
lean_dec(x_97);
x_98 = lean_box(0);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_78, x_99);
lean_dec(x_78);
x_101 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_101, 0, x_72);
lean_ctor_set(x_101, 1, x_98);
lean_ctor_set(x_101, 2, x_93);
x_102 = lean_array_uset(x_79, x_92, x_101);
x_103 = lean_unsigned_to_nat(4u);
x_104 = lean_nat_mul(x_100, x_103);
x_105 = lean_unsigned_to_nat(3u);
x_106 = lean_nat_div(x_104, x_105);
lean_dec(x_104);
x_107 = lean_array_get_size(x_102);
x_108 = lean_nat_dec_le(x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelParams_visitExpr_spec__1___redArg(x_102);
lean_ctor_set(x_4, 1, x_109);
lean_ctor_set(x_4, 0, x_100);
x_5 = x_73;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
goto _start;
}
else
{
lean_ctor_set(x_4, 1, x_102);
lean_ctor_set(x_4, 0, x_100);
x_5 = x_73;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
goto _start;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_4);
x_112 = lean_box(0);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_add(x_78, x_113);
lean_dec(x_78);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_72);
lean_ctor_set(x_115, 1, x_112);
lean_ctor_set(x_115, 2, x_93);
x_116 = lean_array_uset(x_79, x_92, x_115);
x_117 = lean_unsigned_to_nat(4u);
x_118 = lean_nat_mul(x_114, x_117);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_div(x_118, x_119);
lean_dec(x_118);
x_121 = lean_array_get_size(x_116);
x_122 = lean_nat_dec_le(x_120, x_121);
lean_dec(x_121);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectLevelParams_visitExpr_spec__1___redArg(x_116);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_123);
x_4 = x_124;
x_5 = x_73;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
goto _start;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_114);
lean_ctor_set(x_126, 1, x_116);
x_4 = x_126;
x_5 = x_73;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
goto _start;
}
}
}
else
{
lean_dec(x_93);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_72);
x_5 = x_73;
x_6 = x_74;
x_7 = x_75;
x_8 = x_76;
x_9 = x_77;
goto _start;
}
}
block_175:
{
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec(x_132);
x_135 = l_Lean_Meta_Split_isDiscrGenException(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_137 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_136, x_7, x_130);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_133);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_72 = x_131;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_140;
goto block_129;
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_137);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_142 = lean_ctor_get(x_137, 1);
x_143 = lean_ctor_get(x_137, 0);
lean_dec(x_143);
x_144 = l_Lean_Meta_splitTarget_x3f_go___closed__3;
lean_inc(x_131);
x_145 = l_Lean_indentExpr(x_131);
lean_ctor_set_tag(x_137, 7);
lean_ctor_set(x_137, 1, x_145);
lean_ctor_set(x_137, 0, x_144);
x_146 = l_Lean_Meta_splitTarget_x3f_go___closed__5;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_137);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Exception_toMessageData(x_133);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_136, x_151, x_5, x_6, x_7, x_8, x_142);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_72 = x_131;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_153;
goto block_129;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_154 = lean_ctor_get(x_137, 1);
lean_inc(x_154);
lean_dec(x_137);
x_155 = l_Lean_Meta_splitTarget_x3f_go___closed__3;
lean_inc(x_131);
x_156 = l_Lean_indentExpr(x_131);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Meta_splitTarget_x3f_go___closed__5;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_Exception_toMessageData(x_133);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_136, x_163, x_5, x_6, x_7, x_8, x_154);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_72 = x_131;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_165;
goto block_129;
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_133);
x_166 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_167 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_166, x_7, x_130);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_72 = x_131;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_170;
goto block_129;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_167, 1);
lean_inc(x_171);
lean_dec(x_167);
lean_inc(x_131);
x_172 = l_Lean_Meta_Split_mkDiscrGenErrorMsg(x_131);
x_173 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_166, x_172, x_5, x_6, x_7, x_8, x_171);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_72 = x_131;
x_73 = x_5;
x_74 = x_6;
x_75 = x_7;
x_76 = x_8;
x_77 = x_174;
goto block_129;
}
}
}
else
{
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_132;
}
}
block_242:
{
lean_object* x_177; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_177 = l_Lean_Meta_findSplit_x3f(x_3, x_176, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_dec(x_4);
lean_dec(x_3);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_181 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_180, x_7, x_179);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec(x_181);
x_10 = x_184;
goto block_13;
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_181);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_186 = lean_ctor_get(x_181, 1);
x_187 = lean_ctor_get(x_181, 0);
lean_dec(x_187);
x_188 = l_Lean_Meta_splitTarget_x3f_go___closed__7;
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set_tag(x_181, 7);
lean_ctor_set(x_181, 1, x_189);
lean_ctor_set(x_181, 0, x_188);
x_190 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_181);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_180, x_191, x_5, x_6, x_7, x_8, x_186);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_10 = x_193;
goto block_13;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_194 = lean_ctor_get(x_181, 1);
lean_inc(x_194);
lean_dec(x_181);
x_195 = l_Lean_Meta_splitTarget_x3f_go___closed__7;
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_1);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__9;
x_199 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_180, x_199, x_5, x_6, x_7, x_8, x_194);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_10 = x_201;
goto block_13;
}
}
}
else
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_177, 1);
lean_inc(x_202);
lean_dec(x_177);
x_203 = !lean_is_exclusive(x_178);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_178, 0);
x_205 = l_Lean_Expr_isIte(x_204);
if (x_205 == 0)
{
uint8_t x_206; 
x_206 = l_Lean_Expr_isDIte(x_204);
if (x_206 == 0)
{
lean_object* x_207; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_204);
lean_inc(x_1);
x_207 = l_Lean_Meta_Split_splitMatch(x_1, x_204, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
lean_dec(x_204);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_207, 0);
lean_ctor_set(x_178, 0, x_209);
lean_ctor_set(x_207, 0, x_178);
return x_207;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_207, 0);
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_207);
lean_ctor_set(x_178, 0, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_178);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
else
{
uint8_t x_213; 
lean_free_object(x_178);
x_213 = !lean_is_exclusive(x_207);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_214 = lean_ctor_get(x_207, 0);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
lean_inc(x_214);
x_216 = l_Lean_Exception_isInterrupt(x_214);
if (x_216 == 0)
{
uint8_t x_217; 
x_217 = l_Lean_Exception_isRuntime(x_214);
x_130 = x_215;
x_131 = x_204;
x_132 = x_207;
x_133 = x_214;
x_134 = x_217;
goto block_175;
}
else
{
x_130 = x_215;
x_131 = x_204;
x_132 = x_207;
x_133 = x_214;
x_134 = x_216;
goto block_175;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_218 = lean_ctor_get(x_207, 0);
x_219 = lean_ctor_get(x_207, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_207);
lean_inc(x_219);
lean_inc(x_218);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Lean_Exception_isInterrupt(x_218);
if (x_221 == 0)
{
uint8_t x_222; 
x_222 = l_Lean_Exception_isRuntime(x_218);
x_130 = x_219;
x_131 = x_204;
x_132 = x_220;
x_133 = x_218;
x_134 = x_222;
goto block_175;
}
else
{
x_130 = x_219;
x_131 = x_204;
x_132 = x_220;
x_133 = x_218;
x_134 = x_221;
goto block_175;
}
}
}
}
else
{
lean_free_object(x_178);
lean_dec(x_204);
lean_dec(x_4);
lean_dec(x_3);
x_14 = x_202;
goto block_71;
}
}
else
{
lean_free_object(x_178);
lean_dec(x_204);
lean_dec(x_4);
lean_dec(x_3);
x_14 = x_202;
goto block_71;
}
}
else
{
lean_object* x_223; uint8_t x_224; 
x_223 = lean_ctor_get(x_178, 0);
lean_inc(x_223);
lean_dec(x_178);
x_224 = l_Lean_Expr_isIte(x_223);
if (x_224 == 0)
{
uint8_t x_225; 
x_225 = l_Lean_Expr_isDIte(x_223);
if (x_225 == 0)
{
lean_object* x_226; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_223);
lean_inc(x_1);
x_226 = l_Lean_Meta_Split_splitMatch(x_1, x_223, x_5, x_6, x_7, x_8, x_202);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_223);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_227);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_232 = lean_ctor_get(x_226, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_226, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 x_234 = x_226;
} else {
 lean_dec_ref(x_226);
 x_234 = lean_box(0);
}
lean_inc(x_233);
lean_inc(x_232);
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Lean_Exception_isInterrupt(x_232);
if (x_236 == 0)
{
uint8_t x_237; 
x_237 = l_Lean_Exception_isRuntime(x_232);
x_130 = x_233;
x_131 = x_223;
x_132 = x_235;
x_133 = x_232;
x_134 = x_237;
goto block_175;
}
else
{
x_130 = x_233;
x_131 = x_223;
x_132 = x_235;
x_133 = x_232;
x_134 = x_236;
goto block_175;
}
}
}
else
{
lean_dec(x_223);
lean_dec(x_4);
lean_dec(x_3);
x_14 = x_202;
goto block_71;
}
}
else
{
lean_dec(x_223);
lean_dec(x_4);
lean_dec(x_3);
x_14 = x_202;
goto block_71;
}
}
}
}
else
{
uint8_t x_238; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_177);
if (x_238 == 0)
{
return x_177;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_177, 0);
x_240 = lean_ctor_get(x_177, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_177);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_9, x_4, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__4;
x_15 = l_Lean_Meta_splitTarget_x3f_go(x_1, x_2, x_12, x_14, x_3, x_4, x_5, x_6, x_13);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_box(x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_splitTarget_x3f___lam__0___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1), 8, 3);
lean_closure_set(x_10, 0, lean_box(0));
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_splitTarget_x3f___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitTarget_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_splitTarget_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_box(0);
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_introNCore(x_13, x_1, x_15, x_2, x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_21);
{
lean_object* _tmp_2 = x_14;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_20;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_23; 
lean_free_object(x_3);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_32 = l_Lean_Meta_introNCore(x_27, x_1, x_29, x_2, x_31, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_4);
x_3 = x_28;
x_4 = x_36;
x_9 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_40 = x_32;
} else {
 lean_dec_ref(x_32);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_intro1Core(x_12, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Meta_intro1Core(x_23, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Lean_MVarId_revert(x_1, x_2, x_3, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_Meta_Split_splitMatch(x_28, x_4, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
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
lean_dec(x_34);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = lean_ctor_get(x_29, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_29, 1);
lean_inc(x_45);
lean_dec(x_29);
x_19 = x_44;
x_20 = x_45;
goto block_23;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_ctor_get(x_24, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_24, 1);
lean_inc(x_47);
lean_dec(x_24);
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
lean_dec(x_11);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
x_16 = lean_box(2);
x_17 = l_Lean_Meta_splitTarget_x3f___lam__0___closed__4;
x_18 = lean_unbox(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_findSplit_x3f(x_13, x_18, x_17, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_43; lean_object* x_44; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_83; lean_object* x_84; uint8_t x_93; uint8_t x_169; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_28 = x_19;
} else {
 lean_dec_ref(x_19);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_30 = x_20;
} else {
 lean_dec_ref(x_20);
 x_30 = lean_box(0);
}
x_169 = l_Lean_Expr_isIte(x_29);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = l_Lean_Expr_isDIte(x_29);
x_93 = x_170;
goto block_168;
}
else
{
x_93 = x_169;
goto block_168;
}
block_42:
{
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Meta_Split_isDiscrGenException(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_28)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_28;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_32);
lean_dec(x_28);
x_36 = l_Lean_Meta_Split_throwDiscrGenError___redArg(x_29, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_28)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_28;
 lean_ctor_set_tag(x_41, 1);
}
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_31);
return x_41;
}
}
block_47:
{
uint8_t x_45; 
x_45 = l_Lean_Exception_isInterrupt(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Exception_isRuntime(x_43);
x_31 = x_44;
x_32 = x_43;
x_33 = x_46;
goto block_42;
}
else
{
x_31 = x_44;
x_32 = x_43;
x_33 = x_45;
goto block_42;
}
}
block_75:
{
lean_object* x_53; lean_object* x_54; 
x_53 = l_Lean_LocalDecl_toExpr(x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_54 = l_Lean_MVarId_assert(x_2, x_50, x_52, x_53, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_29);
x_57 = l_Lean_Meta_Split_splitMatch(x_55, x_29, x_4, x_5, x_6, x_7, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_61 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1(x_49, x_58, x_60, x_4, x_5, x_6, x_7, x_59);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
if (lean_is_scalar(x_30)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_30;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
if (lean_is_scalar(x_30)) {
 x_67 = lean_alloc_ctor(1, 1, 0);
} else {
 x_67 = x_30;
}
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_30);
x_69 = lean_ctor_get(x_61, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_43 = x_69;
x_44 = x_70;
goto block_47;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_30);
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_dec(x_57);
x_43 = x_71;
x_44 = x_72;
goto block_47;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_30);
x_73 = lean_ctor_get(x_54, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
lean_dec(x_54);
x_43 = x_73;
x_44 = x_74;
goto block_47;
}
}
block_82:
{
if (x_77 == 0)
{
lean_object* x_79; 
lean_dec(x_76);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_2);
x_79 = l_Lean_Meta_Split_throwDiscrGenError___redArg(x_29, x_4, x_5, x_6, x_7, x_78);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_76, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_76, 3);
lean_inc(x_81);
x_48 = x_78;
x_49 = x_77;
x_50 = x_80;
x_51 = x_76;
x_52 = x_81;
goto block_75;
}
}
block_92:
{
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_76 = x_83;
x_77 = x_87;
x_78 = x_86;
goto block_82;
}
else
{
uint8_t x_88; 
lean_dec(x_83);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 0);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_84);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
block_168:
{
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_15);
x_94 = l_Lean_Meta_splitLocalDecl_x3f___lam__1___closed__0;
lean_inc(x_3);
x_95 = lean_array_push(x_94, x_3);
x_96 = lean_box(x_93);
lean_inc(x_29);
lean_inc(x_2);
x_97 = lean_alloc_closure((void*)(l_Lean_Meta_splitLocalDecl_x3f___lam__0___boxed), 9, 4);
lean_closure_set(x_97, 0, x_2);
lean_closure_set(x_97, 1, x_95);
lean_closure_set(x_97, 2, x_96);
lean_closure_set(x_97, 3, x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_98 = l_Lean_commitWhenSome_x3f___at___Lean_Meta_splitIfTarget_x3f_spec__0___redArg(x_97, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_4);
lean_inc(x_3);
x_101 = l_Lean_FVarId_getDecl___redArg(x_3, x_4, x_6, x_7, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_2);
x_104 = l_Lean_MVarId_getType(x_2, x_4, x_5, x_6, x_7, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_LocalDecl_isLet(x_102, x_93);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
lean_inc(x_3);
x_108 = l_Lean_exprDependsOn___at_____private_Lean_Meta_CongrTheorems_0__Lean_Meta_mkCast_go_spec__0___redArg(x_105, x_3, x_5, x_106);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_dec(x_108);
lean_inc(x_4);
x_112 = l_Lean_FVarId_hasForwardDeps(x_3, x_4, x_5, x_6, x_7, x_111);
x_83 = x_102;
x_84 = x_112;
goto block_92;
}
else
{
lean_dec(x_3);
x_83 = x_102;
x_84 = x_108;
goto block_92;
}
}
else
{
lean_dec(x_105);
lean_dec(x_3);
x_76 = x_102;
x_77 = x_107;
x_78 = x_106;
goto block_82;
}
}
else
{
uint8_t x_113; 
lean_dec(x_102);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_104);
if (x_113 == 0)
{
return x_104;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_104, 0);
x_115 = lean_ctor_get(x_104, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_104);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_117 = !lean_is_exclusive(x_101);
if (x_117 == 0)
{
return x_101;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_101, 0);
x_119 = lean_ctor_get(x_101, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_101);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_99);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
}
else
{
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
}
else
{
lean_object* x_121; lean_object* x_122; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_121 = lean_box(0);
x_122 = l_Lean_Meta_splitIfLocalDecl_x3f(x_2, x_3, x_121, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
if (lean_obj_tag(x_123) == 0)
{
uint8_t x_124; 
lean_dec(x_15);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 0);
lean_dec(x_125);
x_126 = lean_box(0);
lean_ctor_set(x_122, 0, x_126);
return x_122;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
lean_dec(x_122);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
else
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_123);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_122);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_123, 0);
x_133 = lean_ctor_get(x_122, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_132, 0);
x_136 = lean_ctor_get(x_132, 1);
x_137 = lean_box(0);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_137);
lean_ctor_set(x_132, 0, x_136);
if (lean_is_scalar(x_15)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_15;
 lean_ctor_set_tag(x_138, 1);
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_132);
lean_ctor_set(x_123, 0, x_138);
return x_122;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_132, 0);
x_140 = lean_ctor_get(x_132, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_132);
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
if (lean_is_scalar(x_15)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_15;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_123, 0, x_143);
return x_122;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_144 = lean_ctor_get(x_123, 0);
x_145 = lean_ctor_get(x_122, 1);
lean_inc(x_145);
lean_dec(x_122);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_148;
 lean_ctor_set_tag(x_150, 1);
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
if (lean_is_scalar(x_15)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_15;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_123, 0, x_151);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_123);
lean_ctor_set(x_152, 1, x_145);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_153 = lean_ctor_get(x_123, 0);
lean_inc(x_153);
lean_dec(x_123);
x_154 = lean_ctor_get(x_122, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_155 = x_122;
} else {
 lean_dec_ref(x_122);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_158 = x_153;
} else {
 lean_dec_ref(x_153);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_158;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_15)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_15;
 lean_ctor_set_tag(x_161, 1);
}
lean_ctor_set(x_161, 0, x_156);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
if (lean_is_scalar(x_155)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_155;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_154);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_15);
x_164 = !lean_is_exclusive(x_122);
if (x_164 == 0)
{
return x_122;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_122, 0);
x_166 = lean_ctor_get(x_122, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_122);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_19);
if (x_171 == 0)
{
return x_19;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_19, 0);
x_173 = lean_ctor_get(x_19, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_19);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_9);
if (x_175 == 0)
{
return x_9;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_9, 0);
x_177 = lean_ctor_get(x_9, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_9);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
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
lean_dec(x_2);
x_11 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_List_mapM_loop___at___Lean_Meta_splitLocalDecl_x3f_spec__1(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_splitLocalDecl_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_splitLocalDecl_x3f___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Split", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_2 = l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6655_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(6655u);
x_2 = l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6655_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__4_spec__4___closed__3;
x_3 = lean_box(0);
x_4 = l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6655_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_splitTarget_x3f_go___closed__1;
x_9 = lean_unbox(x_3);
x_10 = l_Lean_registerTraceClass(x_8, x_9, x_4, x_7);
return x_10;
}
else
{
return x_6;
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
l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_880_ = _init_l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_880_();
lean_mark_persistent(l_Lean_Meta_Split_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_880_);
l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_880_ = _init_l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_880_();
lean_mark_persistent(l_Lean_Meta_Split_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_880_);
if (builtin) {res = l_Lean_Meta_Split_initFn____x40_Lean_Meta_Tactic_Split___hyg_880_(lean_io_mk_world());
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
l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0 = _init_l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__0);
l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget_spec__6___redArg___lam__1___closed__1);
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
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__10____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__11____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__12____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__13____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__14____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__15____x40_Lean_Meta_Tactic_Split___hyg_6655_);
l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6655_ = _init_l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6655_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__16____x40_Lean_Meta_Tactic_Split___hyg_6655_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Split___hyg_6655_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
